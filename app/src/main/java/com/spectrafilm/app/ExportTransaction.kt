/*
 * Spektrafilm for Android — crash-recoverable, digest-verified export commit. GPLv3.
 */
package com.spectrafilm.app

import android.content.ContentValues
import android.content.ContentUris
import android.content.Context
import android.net.Uri
import android.os.Build
import android.provider.MediaStore
import androidx.annotation.RequiresApi
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.IOException
import java.io.InputStream
import java.io.OutputStream
import java.security.MessageDigest
import java.util.UUID
import java.util.concurrent.CancellationException
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicReference

internal data class EncodedArtifact(
    val file: File,
    val length: Long,
    val sha256: String,
) {
    companion object {
        fun fromCompletedFile(
            file: File,
            encoderByteCount: Long = file.length(),
            isCancelled: () -> Boolean = { false },
        ): EncodedArtifact {
            if (!file.isFile) throw IOException("encoded artifact is missing: $file")
            val actualLength = file.length()
            if (encoderByteCount <= 0L) throw IOException("encoder returned no bytes")
            if (encoderByteCount != actualLength) {
                throw IOException("encoder returned $encoderByteCount bytes but staged file has $actualLength")
            }
            val measured = digest(file, isCancelled)
            return EncodedArtifact(file, measured.length, measured.sha256)
        }
    }
}

internal data class ExportDestinationSpec(
    val displayName: String,
    val mimeType: String,
    val relativePath: String,
) {
    init {
        require(displayName.isNotBlank() && displayName.length <= 255)
        require('/' !in displayName && '\\' !in displayName && '\u0000' !in displayName)
        require(mimeType.startsWith("image/") && mimeType.length <= 127)
        require(relativePath.isNotBlank() && relativePath.length <= 512)
    }
}

internal enum class StoredExportState { PENDING, PUBLISHED, MISSING, UNKNOWN }

internal class ExportReconciliationPendingException(
    message: String,
    cause: Throwable? = null,
) : IOException(message, cause)

internal interface PendingExportBackend {
    fun reserve(spec: ExportDestinationSpec): String
    fun openWrite(token: String): OutputStream
    fun openRead(token: String): InputStream
    fun publish(token: String, spec: ExportDestinationSpec): Int
    fun delete(token: String): Int
    fun state(token: String): StoredExportState
    /** Provider-owned discovery closes the insert-before-journal process-kill window. */
    fun pendingTokens(): Set<String> = emptySet()
}

/**
 * Reserve a pending MediaStore row that the provider actually kept, trying each
 * candidate [spec] in order.
 *
 * This exists because an insert can succeed and the row can still disappear. MediaStore's
 * Images collection only indexes media types the platform knows; on some OEM providers
 * (observed on a vivo/Android 16 device) `image/tiff` returns a URI that is dropped
 * immediately, so the very next `openOutputStream` throws
 * `FileNotFoundException: No item at content://...` -- *after* a full-resolution render,
 * with a message that names neither the format nor the provider. That is what made a
 * 16-bit TIFF export look like a render/memory failure while a 16-bit PNG of the same
 * frame published fine: same code path, same size, only the MIME type differs.
 *
 * [specs] are tried in order; the row from a candidate that did not stick is deleted when
 * the provider says it is MISSING. An UNKNOWN state (a query that threw) is deliberately
 * NOT treated as a licence to delete: the next-start recovery sweep owns those rows.
 *
 * Returns the token and the spec whose row survived.
 */
internal fun reserveVisiblePendingRow(
    specs: List<ExportDestinationSpec>,
    insert: (ExportDestinationSpec) -> String?,
    state: (String) -> StoredExportState,
    delete: (String) -> Int,
    confirmAttempts: Int = 5,
    waitMillis: Long = 20L,
    sleeper: (Long) -> Unit = { millis -> if (millis > 0L) Thread.sleep(millis) },
): Pair<String, ExportDestinationSpec> {
    require(specs.isNotEmpty()) { "at least one export destination is required" }
    var lastToken: String? = null
    var lastObserved = StoredExportState.UNKNOWN
    for ((index, spec) in specs.withIndex()) {
        val token = insert(spec)
            ?: throw IOException("MediaStore insert failed for ${spec.mimeType} in ${spec.relativePath}")
        lastToken = token
        var observed = StoredExportState.UNKNOWN
        for (attempt in 0 until confirmAttempts.coerceAtLeast(1)) {
            observed = state(token)
            if (observed == StoredExportState.PENDING) break
            if (attempt < confirmAttempts - 1) sleeper(waitMillis)
        }
        lastObserved = observed
        // Only a DEFINITIVE absence moves on. PENDING is the expected answer; UNKNOWN (a
        // query that threw) and PUBLISHED are not evidence of anything, and turning them
        // into a second insert would break devices where the first one works today.
        if (observed != StoredExportState.MISSING) {
            if (index > 0) Diag.i("export destination fell back to ${spec.relativePath} (${spec.mimeType})")
            return token to spec
        }
        Diag.w(
            "MediaStore dropped the pending row for ${spec.mimeType} in " +
                "${spec.relativePath} (state=$observed)",
        )
        runCatching { delete(token) }
    }
    throw IOException(
        "MediaStore kept none of the candidate destinations for " +
            specs.joinToString { "${it.mimeType} in ${it.relativePath}" } +
            " (last state=$lastObserved, token=$lastToken)",
    )
}

internal interface PendingExportJournal {
    fun add(token: String)
    fun remove(token: String)
    fun tokens(): Set<String>
}

internal data class ExportRecoveryReport(
    val examined: Int,
    val removedPending: Int,
    val retiredCommittedOrMissing: Int,
    val retainedForRetry: Int,
    val removedAbandonedStages: Int = 0,
    val retainedAbandonedStages: Int = 0,
)

internal data class AbandonedExportStageRecoveryReport(
    val examined: Int,
    val removed: Int,
    val retained: Int,
)

/**
 * Synchronous commit state machine. Call from Dispatchers.IO. A success is returned
 * only after destination close, readback length/SHA-256 verification, one publish
 * update, and confirmation that the row is no longer pending.
 */
internal class ExportTransaction(
    private val backend: PendingExportBackend,
    private val journal: PendingExportJournal,
) {
    fun commit(
        artifact: EncodedArtifact,
        spec: ExportDestinationSpec,
        isCancelled: () -> Boolean = { false },
        onPublished: (String) -> Unit = {},
    ): String {
        throwIfExportCancelled(isCancelled)
        verifyArtifact(artifact)
        throwIfExportCancelled(isCancelled)
        val token = backend.reserve(spec)
        // Step markers: when publication fails, the log line names the step that failed
        // instead of surfacing only "No item at content://..." with no context.
        Diag.i("export destination reserved")
        var publicationReported = false
        fun reportPublication() {
            if (publicationReported) return
            publicationReported = true
            onPublished(token)
        }
        try {
            journal.add(token)
        } catch (failure: Throwable) {
            val deleted = runCatching { backend.delete(token) }
            deleted.exceptionOrNull()?.let(failure::addSuppressed)
            val after = runCatching { backend.state(token) }.getOrDefault(StoredExportState.UNKNOWN)
            if (deleted.getOrDefault(0) != 1 && after != StoredExportState.MISSING) {
                failure.addSuppressed(
                    IOException("unjournaled tagged pending row will be reconciled at next recovery"),
                )
            }
            throw failure
        }

        try {
            throwIfExportCancelled(isCancelled)
            val copied = copyAndDigest(artifact.file, backend.openWrite(token), isCancelled)
            Diag.i("export destination wrote ${copied.length} bytes")
            if (copied.length != artifact.length || copied.sha256 != artifact.sha256) {
                throw IOException("destination write digest differs from staged artifact")
            }

            val readback = backend.openRead(token).use { digest(it, isCancelled) }
            Diag.i("export destination readback verified ${readback.length} bytes")
            if (readback.length != artifact.length || readback.sha256 != artifact.sha256) {
                throw IOException("destination readback digest differs from staged artifact")
            }

            // Cancellation must win before the provider's publication linearization point.
            // If it arrives while publish() is in flight, the catch path observes provider state:
            // a confirmed PUBLISHED row still wins, while PENDING is deleted below.
            throwIfExportCancelled(isCancelled)
            val updated = backend.publish(token, spec)
            Diag.i("export destination published ($updated row)")
            if (updated != 1) throw IOException("MediaStore publish updated $updated rows; expected 1")
            if (backend.state(token) != StoredExportState.PUBLISHED) {
                throw IOException("destination did not confirm published state")
            }
            // This callback is inside the synchronous transaction, immediately after provider
            // confirmation and before any caller can hit a cancellable dispatcher return.
            reportPublication()
            journal.remove(token)
            return token
        } catch (failure: Throwable) {
            val observed = runCatching { backend.state(token) }.getOrDefault(StoredExportState.UNKNOWN)
            // Once the provider confirms publication, commit wins over a late cancellation or
            // journal-cleanup failure. Recovery will idempotently retire a leftover journal token.
            if (observed == StoredExportState.PUBLISHED) {
                reportPublication()
                runCatching { journal.remove(token) }
                return token
            }
            if (observed == StoredExportState.UNKNOWN) {
                throw ExportReconciliationPendingException(
                    "export outcome is indeterminate; restart or reconcile before retrying",
                    failure,
                )
            }
            cleanupUncommitted(token, observed, failure)
            throw failure
        }
    }

    fun recover(): ExportRecoveryReport {
        var removed = 0
        var retired = 0
        var retained = 0
        val journaledTokens = journal.tokens()
        // Discovery is the only way to see a process-kill between provider insert and
        // durable journal add. Treat an unavailable provider query as reconciliation
        // failure instead of silently permitting another export.
        val discoveredTokens = backend.pendingTokens()
        val tokens = linkedSetOf<String>().apply {
            addAll(journaledTokens)
            addAll(discoveredTokens)
        }
        for (token in tokens) {
            val wasJournaled = token in journaledTokens
            when (runCatching { backend.state(token) }.getOrDefault(StoredExportState.UNKNOWN)) {
                StoredExportState.PUBLISHED, StoredExportState.MISSING -> {
                    if (!wasJournaled) {
                        retired++
                    } else {
                        runCatching { journal.remove(token) }
                            .onSuccess { retired++ }
                            .onFailure { retained++ }
                    }
                }
                StoredExportState.PENDING -> {
                    val deleted = runCatching { backend.delete(token) }.getOrDefault(0)
                    val after = runCatching { backend.state(token) }.getOrDefault(StoredExportState.UNKNOWN)
                    if (deleted == 1 || after == StoredExportState.MISSING) {
                        if (!wasJournaled) {
                            removed++
                        } else {
                            runCatching { journal.remove(token) }
                                .onSuccess { removed++ }
                                .onFailure { retained++ }
                        }
                    } else {
                        retained++
                    }
                }
                StoredExportState.UNKNOWN -> retained++
            }
        }
        return ExportRecoveryReport(tokens.size, removed, retired, retained)
    }

    private fun cleanupUncommitted(
        token: String,
        observed: StoredExportState,
        primary: Throwable,
    ) {
        if (observed == StoredExportState.MISSING) {
            runCatching { journal.remove(token) }.exceptionOrNull()?.let(primary::addSuppressed)
            return
        }
        if (observed != StoredExportState.PENDING) {
            // Unknown may already be published; retain the journal for safe next-start recovery.
            return
        }
        val deleted = runCatching { backend.delete(token) }
        deleted.exceptionOrNull()?.let(primary::addSuppressed)
        val after = runCatching { backend.state(token) }.getOrDefault(StoredExportState.UNKNOWN)
        if (deleted.getOrDefault(0) == 1 || after == StoredExportState.MISSING) {
            runCatching { journal.remove(token) }.exceptionOrNull()?.let(primary::addSuppressed)
        } else {
            primary.addSuppressed(IOException("pending destination cleanup will be retried"))
        }
    }

    /**
     * Cheap pre-reservation check: a missing or resized stage fails before a MediaStore row
     * exists. It deliberately does NOT re-hash the file. The artifact's digest was measured
     * moments earlier (or validated on cache read), and [copyAndDigest] hashes the very bytes
     * it copies and compares them to [EncodedArtifact.sha256], so a stage whose content changed
     * after encoding is still rejected -- after reservation, where the pending row is deleted.
     * The extra full read here cost one more pass over a 70 MB TIFF on every export.
     */
    private fun verifyArtifact(artifact: EncodedArtifact) {
        if (!artifact.file.isFile) throw IOException("staged artifact disappeared")
        if (artifact.file.length() != artifact.length) {
            throw IOException("staged artifact changed after encoding")
        }
    }

    private fun copyAndDigest(
        file: File,
        output: OutputStream,
        isCancelled: () -> Boolean,
    ): DigestAndLength {
        val md = MessageDigest.getInstance("SHA-256")
        var count = 0L
        output.use { sink ->
            FileInputStream(file).use { source ->
                val buffer = ByteArray(COPY_BUFFER_BYTES)
                while (true) {
                    throwIfExportCancelled(isCancelled)
                    val read = source.read(buffer)
                    if (read < 0) break
                    sink.write(buffer, 0, read)
                    md.update(buffer, 0, read)
                    count += read
                    throwIfExportCancelled(isCancelled)
                }
            }
            sink.flush()
            if (sink is FileOutputStream) sink.fd.sync()
        }
        return DigestAndLength(count, md.digest().toHex())
    }
}

@RequiresApi(Build.VERSION_CODES.Q)
internal class AndroidPendingExportBackend(context: Context) : PendingExportBackend {
    private val resolver = context.applicationContext.contentResolver
    private val ownerPackageName = context.applicationContext.packageName

    override fun reserve(spec: ExportDestinationSpec): String {
        check(Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q)
        val (token, chosen) = reserveVisiblePendingRow(
            specs = candidateSpecs(spec),
            insert = ::insertPendingRow,
            state = ::state,
            delete = ::delete,
        )
        Diag.i("export destination ${chosen.relativePath} (${chosen.mimeType})")
        return token
    }

    /**
     * Where a pending row may be created. The Images collection is tried first so a device
     * that indexes the type keeps putting it in Pictures; a type the platform media index
     * does not know (TIFF) can be dropped there, so Downloads is offered as the second,
     * type-agnostic destination. Indexed types get one candidate and behave exactly as
     * before.
     */
    private fun candidateSpecs(spec: ExportDestinationSpec): List<ExportDestinationSpec> =
        if (spec.mimeType.lowercase() in PLATFORM_INDEXED_IMAGE_MIME_TYPES) {
            listOf(spec)
        } else {
            listOf(spec, spec.copy(relativePath = MEDIASTORE_DOWNLOADS_RELATIVE_PATH))
        }

    @RequiresApi(Build.VERSION_CODES.Q)
    private fun insertPendingRow(spec: ExportDestinationSpec): String? {
        val extension = spec.displayName.substringAfterLast('.', "tmp")
            .filter { it.isLetterOrDigit() }
            .take(12)
            .ifEmpty { "tmp" }
        val values = ContentValues().apply {
            put(
                MediaStore.MediaColumns.DISPLAY_NAME,
                "$MEDIASTORE_PENDING_NAME_PREFIX${UUID.randomUUID()}.$extension",
            )
            put(MediaStore.MediaColumns.MIME_TYPE, spec.mimeType)
            put(MediaStore.MediaColumns.RELATIVE_PATH, spec.relativePath)
            put(MediaStore.MediaColumns.IS_PENDING, 1)
        }
        return resolver.insert(collectionFor(spec.relativePath), values)?.toString()
    }

    private fun collectionFor(relativePath: String): Uri =
        if (relativePath.startsWith(MEDIASTORE_DOWNLOADS_PREFIX)) {
            MediaStore.Downloads.EXTERNAL_CONTENT_URI
        } else {
            MediaStore.Images.Media.EXTERNAL_CONTENT_URI
        }

    override fun openWrite(token: String): OutputStream =
        resolver.openOutputStream(Uri.parse(token), "w")
            ?: throw IOException("could not open pending MediaStore output")

    override fun openRead(token: String): InputStream =
        resolver.openInputStream(Uri.parse(token))
            ?: throw IOException("could not reopen pending MediaStore output")

    // MediaColumns, not Images.Media: the row may live in either collection and both use
    // the same column names, so the update is written once.
    override fun publish(token: String, spec: ExportDestinationSpec): Int = resolver.update(
        Uri.parse(token),
        ContentValues().apply {
            put(MediaStore.MediaColumns.DISPLAY_NAME, spec.displayName)
            put(MediaStore.MediaColumns.IS_PENDING, 0)
        },
        null,
        null,
    )

    override fun delete(token: String): Int = resolver.delete(Uri.parse(token), null, null)

    @Suppress("DEPRECATION")
    override fun pendingTokens(): Set<String> = buildSet {
        addAll(pendingTokens(MediaStore.Images.Media.EXTERNAL_CONTENT_URI,
                             MEDIASTORE_EXPORT_RELATIVE_PATH))
        // Rows this backend may have created in Downloads (types the Images collection
        // does not index) have to be discoverable too, or a process death mid-write would
        // leak a pending item forever.
        addAll(pendingTokens(MediaStore.Downloads.EXTERNAL_CONTENT_URI,
                             MEDIASTORE_DOWNLOADS_RELATIVE_PATH))
    }

    @Suppress("DEPRECATION")
    private fun pendingTokens(collectionUri: Uri, relativePath: String): Set<String> {
        val collection = MediaStore.setIncludePending(collectionUri)
        val cursor = resolver.query(
            collection,
            arrayOf(MediaStore.MediaColumns._ID),
            "${MediaStore.MediaColumns.IS_PENDING}=? AND " +
                "${MediaStore.MediaColumns.OWNER_PACKAGE_NAME}=? AND " +
                "(${MediaStore.MediaColumns.RELATIVE_PATH}=? OR ${MediaStore.MediaColumns.RELATIVE_PATH}=?) AND " +
                "${MediaStore.MediaColumns.DISPLAY_NAME} LIKE ?",
            arrayOf(
                "1",
                ownerPackageName,
                relativePath,
                "$relativePath/",
                "$MEDIASTORE_PENDING_NAME_PREFIX%",
            ),
            null,
        ) ?: throw IOException("MediaStore pending-row discovery returned no cursor")
        return cursor.use {
            buildSet {
                while (it.moveToNext()) {
                    add(ContentUris.withAppendedId(collectionUri, it.getLong(0)).toString())
                }
            }
        }
    }

    @Suppress("DEPRECATION")
    override fun state(token: String): StoredExportState {
        return try {
            val parsed = Uri.parse(token)
            // A syntactically foreign journal value cannot name a row owned by this backend.
            // Provider/query exceptions for an otherwise valid MediaStore URI remain UNKNOWN:
            // an exception is not evidence that the row is absent.
            if (parsed.scheme != "content" || parsed.authority != MediaStore.AUTHORITY) {
                return StoredExportState.MISSING
            }
            val uri = MediaStore.setIncludePending(parsed)
            val cursor = resolver.query(
                uri,
                arrayOf(MediaStore.Images.Media.IS_PENDING),
                null,
                null,
                null,
            ) ?: return StoredExportState.UNKNOWN
            cursor.use {
                if (!it.moveToFirst()) StoredExportState.MISSING
                else if (it.getInt(0) == 0) StoredExportState.PUBLISHED else StoredExportState.PENDING
            }
        } catch (_: SecurityException) {
            StoredExportState.UNKNOWN
        } catch (_: IllegalArgumentException) {
            StoredExportState.UNKNOWN
        }
    }
}

internal class SharedPreferencesPendingExportJournal(context: Context) : PendingExportJournal {
    private val prefs = context.applicationContext.getSharedPreferences(PREFS, Context.MODE_PRIVATE)

    override fun add(token: String) = synchronized(PROCESS_LOCK) {
        val next = tokens().toMutableSet().apply { add(token) }
        if (next.size > MAX_TOKENS) throw IOException("pending export journal is full")
        commit(next)
    }

    override fun remove(token: String) = synchronized(PROCESS_LOCK) {
        val next = tokens().toMutableSet().apply { remove(token) }
        commit(next)
    }

    override fun tokens(): Set<String> = synchronized(PROCESS_LOCK) {
        prefs.getStringSet(KEY_TOKENS, emptySet())?.toSet() ?: emptySet()
    }

    private fun commit(tokens: Set<String>) {
        check(prefs.edit().putStringSet(KEY_TOKENS, tokens.toSet()).commit()) {
            "could not commit pending export journal"
        }
    }

    private companion object {
        val PROCESS_LOCK = Any()
        const val PREFS = "pending_media_exports_v1"
        const val KEY_TOKENS = "uri_tokens"
        const val MAX_TOKENS = 128
    }
}

@RequiresApi(Build.VERSION_CODES.Q)
internal fun mediaStoreExportTransaction(context: Context): ExportTransaction = ExportTransaction(
    AndroidPendingExportBackend(context),
    SharedPreferencesPendingExportJournal(context),
)

internal fun recoverPendingMediaStoreExports(context: Context): ExportRecoveryReport =
    if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
        synchronized(mediaStoreExportProcessLock) {
            mediaStoreExportTransaction(context).recover()
        }
    } else {
        ExportRecoveryReport(0, 0, 0, 0)
    }

internal class ProcessStageRecoveryGate(val cutoffMillis: Long) {
    private val started = AtomicBoolean(false)

    init {
        require(cutoffMillis > 0L)
    }

    /** Marks the stage sweep consumed even when [operation] throws; it is never safe to retry it. */
    fun <T> runOnce(operation: (Long) -> T): T? {
        if (!started.compareAndSet(false, true)) return null
        return operation(cutoffMillis)
    }
}

private val processStageRecoveryGate = AtomicReference<ProcessStageRecoveryGate?>(null)
private val exportProviderRecoveryInFlight = AtomicBoolean(false)
private val exportProviderRecoveryCompleted = AtomicBoolean(false)

/** Capture the first Activity's cutoff synchronously; later recreations cannot move it forward. */
internal fun registerExportProcessStageCutoff(candidateMillis: Long): Long {
    val candidate = ProcessStageRecoveryGate(candidateMillis)
    processStageRecoveryGate.compareAndSet(null, candidate)
    return checkNotNull(processStageRecoveryGate.get()).cutoffMillis
}

/** Run only once per process so an Activity recreation cannot race a live export. */
internal fun recoverPendingMediaStoreExportsOnce(
    context: Context,
    priorProcessCutoffMillis: Long,
): ExportRecoveryReport? {
    val cutoff = registerExportProcessStageCutoff(priorProcessCutoffMillis)
    val stageRecovery = checkNotNull(processStageRecoveryGate.get()).runOnce {
        val abandoned = recoverAbandonedExportStages(context.cacheDir, cutoff)
        val legacyAbandoned = recoverAbandonedLegacyExportStages(context, cutoff)
        AbandonedExportStageRecoveryReport(
            examined = abandoned.examined + legacyAbandoned.examined,
            removed = abandoned.removed + legacyAbandoned.removed,
            retained = abandoned.retained + legacyAbandoned.retained,
        )
    }
    if (exportProviderRecoveryCompleted.get()) {
        return stageRecovery?.let {
            ExportRecoveryReport(0, 0, 0, 0, it.removed, it.retained)
        }
    }
    if (!exportProviderRecoveryInFlight.compareAndSet(false, true)) {
        return stageRecovery?.let {
            ExportRecoveryReport(0, 0, 0, 0, it.removed, it.retained)
        }
    }
    return try {
        recoverPendingMediaStoreExports(context).also {
            exportProviderRecoveryCompleted.set(true)
        }.copy(
            removedAbandonedStages = stageRecovery?.removed ?: 0,
            retainedAbandonedStages = stageRecovery?.retained ?: 0,
        )
    } finally {
        exportProviderRecoveryInFlight.set(false)
    }
}

/**
 * Delete only app-private export stages created before this process's first Activity.
 * The cutoff prevents asynchronous startup recovery from touching a live current-process stage.
 */
internal fun recoverAbandonedExportStages(
    cacheDir: File,
    priorProcessCutoffMillis: Long,
): AbandonedExportStageRecoveryReport {
    require(priorProcessCutoffMillis > 0L)
    var examined = 0
    var removed = 0
    var retained = 0
    cacheDir.listFiles()?.forEach { candidate ->
        if (
            candidate.isFile &&
            candidate.name.startsWith(EXPORT_STAGE_PREFIX) &&
            candidate.name.endsWith(EXPORT_STAGE_SUFFIX) &&
            candidate.lastModified() < priorProcessCutoffMillis
        ) {
            examined++
            if (candidate.delete()) removed++ else retained++
        }
    }
    return AbandonedExportStageRecoveryReport(examined, removed, retained)
}

@RequiresApi(Build.VERSION_CODES.Q)
internal fun publishStagedImage(
    context: Context,
    artifact: EncodedArtifact,
    displayName: String,
    mimeType: String,
    isCancelled: () -> Boolean = { false },
    onPublished: (Uri) -> Unit = {},
): Uri {
    check(Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q)
    val token = synchronized(mediaStoreExportProcessLock) {
        val transaction = mediaStoreExportTransaction(context)
        val recovery = transaction.recover()
        if (recovery.retainedForRetry > 0) {
            throw ExportReconciliationPendingException(
                "a previous export still requires provider reconciliation",
            )
        }
        transaction.commit(
            artifact,
            ExportDestinationSpec(
                displayName = displayName,
                mimeType = mimeType,
                relativePath = MEDIASTORE_EXPORT_RELATIVE_PATH,
            ),
            isCancelled = isCancelled,
            onPublished = { token -> onPublished(Uri.parse(token)) },
        )
    }
    return Uri.parse(token)
}

private data class DigestAndLength(val length: Long, val sha256: String)

private fun digest(
    file: File,
    isCancelled: () -> Boolean = { false },
): DigestAndLength = FileInputStream(file).use { digest(it, isCancelled) }

private fun digest(
    input: InputStream,
    isCancelled: () -> Boolean = { false },
): DigestAndLength {
    val md = MessageDigest.getInstance("SHA-256")
    var count = 0L
    val buffer = ByteArray(COPY_BUFFER_BYTES)
    while (true) {
        throwIfExportCancelled(isCancelled)
        val read = input.read(buffer)
        if (read < 0) break
        md.update(buffer, 0, read)
        count += read
        throwIfExportCancelled(isCancelled)
    }
    return DigestAndLength(count, md.digest().toHex())
}

private fun throwIfExportCancelled(isCancelled: () -> Boolean) {
    if (isCancelled()) throw CancellationException("export publication cancelled")
}

private fun ByteArray.toHex(): String = joinToString("") { "%02x".format(it) }

private const val COPY_BUFFER_BYTES = 256 * 1024
private const val EXPORT_STAGE_PREFIX = "spectrafilm-export-"
private const val EXPORT_STAGE_SUFFIX = ".part"
private const val MEDIASTORE_EXPORT_RELATIVE_PATH = "Pictures/Spektrafilm"
/**
 * Second-choice destination for a type the platform media index does not know (TIFF).
 * Downloads accepts any file type on every provider, and a 16-bit master is a file to
 * hand to a desktop editor, not a picture the gallery can show.
 */
private const val MEDIASTORE_DOWNLOADS_RELATIVE_PATH = "Download/Spektrafilm"
private const val MEDIASTORE_DOWNLOADS_PREFIX = "Download/"
/** Media types Android's media index knows; anything else may be discarded on insert. */
private val PLATFORM_INDEXED_IMAGE_MIME_TYPES = setOf(
    "image/jpeg",
    "image/jpg",
    "image/png",
    "image/webp",
    "image/gif",
    "image/heic",
    "image/heif",
    "image/avif",
    "image/bmp",
)
private const val MEDIASTORE_PENDING_NAME_PREFIX = "Spektrafilm-pending-tx-"
private val mediaStoreExportProcessLock = Any()
