package souther.compiler.diag;

import java.util.List;

/**
 * A compile error with a source position. Carries an error code (e.g. {@code E1101})
 * when one applies (spec section 22), otherwise a bare message for lex/parse errors.
 *
 * <p>The exception now wraps a structured {@link Diagnostic}. {@link #getMessage()} still returns the
 * one-line {@code line:col code: message} form (so existing callers and tests are unchanged), while a
 * renderer can take {@link #diagnostic()} and produce the Elm-style snippet or JSON. A site that has
 * not been moved onto a catalog key throws with a literal message, wrapped as a
 * {@link Diagnostic#literal literal} diagnostic.
 *
 * <p>Most phases stop at the first error, so the exception carries one diagnostic. A phase that finds
 * several independent errors at once — every failing {@code example} row — throws them all through
 * {@link #diagnostics()}, and the CLI and the annotation processor print each. {@link #diagnostic()}
 * is then the first: the one a single-diagnostic caller reads.
 */
public class CompileException extends RuntimeException {

    /** A position is a line and a column, so a compile that was handed several sources also has to
     *  say which one — otherwise there is nothing to quote the line from. */
    private static final String NO_SOURCE = Located.NO_SOURCE;

    private final transient List<Diagnostic> diagnostics;
    /** One entry per diagnostic: which source it came from, or {@link #NO_SOURCE}. A compile that
     *  reports several modules at once has a diagnostic per module, and each quotes its own file.
     *  Parallel to {@link #diagnostics}, so the order here is that list's order and nothing else. */
    private final transient List<String> sources;

    public CompileException(SourcePos pos, String message) {
        this(Diagnostic.literal(pos, message), format(pos, null, message));
    }

    /** Throws with a fully structured diagnostic (a migrated site). */
    public CompileException(Diagnostic diagnostic, String legacyMessage) {
        this(List.of(diagnostic), legacyMessage, NO_SOURCE);
    }

    private CompileException(List<Diagnostic> diagnostics, String legacyMessage, String sourceId) {
        this(diagnostics, legacyMessage, java.util.Collections.nCopies(diagnostics.size(), sourceId));
    }

    private CompileException(List<Diagnostic> diagnostics, String legacyMessage, List<String> sources) {
        super(legacyMessage);
        this.diagnostics = diagnostics;
        // Not List.copyOf: an entry is NO_SOURCE for a diagnostic that names none, and that is null.
        this.sources = java.util.Collections.unmodifiableList(new java.util.ArrayList<>(sources));
    }

    /**
     * A migrated throw site: the structured {@code diagnostic} drives the Elm-style / JSON rendering,
     * while {@code legacyBody} keeps {@link #getMessage()} returning the same one-line form as before
     * (so callers and tests that read the message text are unchanged).
     */
    public static CompileException of(Diagnostic diagnostic, String legacyBody) {
        return new CompileException(diagnostic,
                format(diagnostic.pos(), diagnostic.code(), legacyBody));
    }

    /**
     * A throw site that found several errors in one pass and reports each; {@code diagnostics} must
     * not be empty. The first drives {@link #pos()}, {@link #code()} and the one-line
     * {@code legacyBody} prefix; a renderer walks {@link #diagnostics()} and prints them all.
     */
    public static CompileException ofAll(List<Diagnostic> diagnostics, String legacyBody) {
        if (diagnostics == null || diagnostics.isEmpty()) {
            // An error with nothing to report is a caller that failed to check whether it found
            // anything; say so here rather than at the `get(0)` below.
            throw new IllegalArgumentException("a compile error carries at least one diagnostic");
        }
        Diagnostic first = diagnostics.get(0);
        return new CompileException(List.copyOf(diagnostics),
                format(first.pos(), first.code(), legacyBody), NO_SOURCE);
    }

    /**
     * Several errors found across several sources, each tagged with the source it came from —
     * a multi-module compile reporting every module's failing examples rather than the first
     * module's. {@code sources} has one entry per diagnostic, {@link Located#NO_SOURCE} for one that
     * names none.
     */
    public static CompileException ofAllInSources(List<Diagnostic> diagnostics, List<String> sources,
                                                  String legacyBody) {
        if (diagnostics == null || diagnostics.isEmpty()) {
            throw new IllegalArgumentException("a compile error carries at least one diagnostic");
        }
        if (sources.size() != diagnostics.size()) {
            throw new IllegalArgumentException("one source per diagnostic");
        }
        Diagnostic first = diagnostics.get(0);
        return new CompileException(List.copyOf(diagnostics),
                format(first.pos(), first.code(), legacyBody), sources);
    }

    public SourcePos pos() {
        Diagnostic d = diagnostic();
        return d == null ? null : d.pos();
    }

    public String code() {
        Diagnostic d = diagnostic();
        return d == null ? null : d.code();
    }

    /** The structured diagnostic behind this error, for a renderer; the first when the error carries
     * several. */
    public Diagnostic diagnostic() {
        List<Diagnostic> all = diagnostics();
        return all.isEmpty() ? null : all.get(0);
    }

    /** Every diagnostic this error carries, in the order they were found — one for most phases,
     * several when a pass reports each of its independent failures. Empty when the structured form
     * did not survive (the field is transient, so a deserialized error has only its message). */
    public List<Diagnostic> diagnostics() {
        return diagnostics == null ? List.of() : diagnostics;
    }

    /**
     * Which of the sources a multi-module compile was handed this error came from, or null when it
     * names none. Untagged covers a single-source compile — where the caller knows the file — and an
     * error a linked compile cannot pin on one source, such as a failing example the compiler merged
     * in from an {@code examples for} file. A caller reads null as "quote no line", never as "the
     * first source".
     */
    public String sourceId() {
        return sources.isEmpty() ? NO_SOURCE : sources.get(0);
    }

    /** Which source the {@code i}-th of {@link #diagnostics()} came from, or null when it names
     *  none. A renderer walking the list quotes each diagnostic's own file. */
    public String sourceIdOf(int i) {
        return sources == null || i >= sources.size() ? NO_SOURCE : sources.get(i);
    }

    /** Every diagnostic this error carries, each with the source it came from — what a renderer
     *  walks, and the shape a warning arrives in too, so one loop renders both. */
    public List<Located> locatedDiagnostics() {
        List<Diagnostic> ds = diagnostics();
        List<Located> located = new java.util.ArrayList<>(ds.size());
        for (int i = 0; i < ds.size(); i++) {
            located.add(new Located(ds.get(i), sourceIdOf(i)));
        }
        return List.copyOf(located);
    }

    /**
     * The same error, tagged with the source being compiled when it was thrown. The first tag wins:
     * an inner phase that already named its source keeps it, so a surrounding loop may tag freely.
     */
    public CompileException inSource(String sourceId) {
        if (sourceId == null || sources.stream().allMatch(src -> src != NO_SOURCE)) {
            return this;   // already named, or nothing to name it with
        }
        List<String> filled = sources.stream().map(src -> src == NO_SOURCE ? sourceId : src).toList();
        CompileException tagged = new CompileException(diagnostics, getMessage(), filled);
        tagged.setStackTrace(getStackTrace());
        return tagged;
    }

    private static String format(SourcePos pos, String code, String message) {
        String where = pos == null ? "" : pos + " ";
        String c = code == null ? "" : code + ": ";
        return where + c + message;
    }
}
