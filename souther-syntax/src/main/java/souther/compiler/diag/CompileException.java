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
    private static final int NO_SOURCE = -1;

    private final transient List<Diagnostic> diagnostics;
    private final int sourceIndex;

    public CompileException(SourcePos pos, String message) {
        this(pos, null, message);
    }

    public CompileException(SourcePos pos, String code, String message) {
        this(Diagnostic.literal(pos, code, message), format(pos, code, message));
    }

    /** Throws with a fully structured diagnostic (a migrated site). */
    public CompileException(Diagnostic diagnostic, String legacyMessage) {
        this(List.of(diagnostic), legacyMessage, NO_SOURCE);
    }

    private CompileException(List<Diagnostic> diagnostics, String legacyMessage, int sourceIndex) {
        super(legacyMessage);
        this.diagnostics = diagnostics;
        this.sourceIndex = sourceIndex;
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
        Diagnostic first = diagnostics.get(0);
        return new CompileException(List.copyOf(diagnostics),
                format(first.pos(), first.code(), legacyBody), NO_SOURCE);
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
     * Which of the sources a multi-module compile was handed this error came from, or {@code -1} when
     * it names none. Untagged covers a single-source compile — where the caller knows the file — and
     * an error a linked compile cannot pin on one source, such as a failing example the compiler
     * merged in from an {@code examples for} file. A caller reads {@code -1} as "quote no line",
     * never as "the first source".
     */
    public int sourceIndex() {
        return sourceIndex;
    }

    /**
     * The same error, tagged with the source being compiled when it was thrown. The first tag wins:
     * an inner phase that already named its source keeps it, so a surrounding loop may tag freely.
     */
    public CompileException inSource(int index) {
        if (sourceIndex != NO_SOURCE || index < 0) {
            return this;
        }
        CompileException tagged = new CompileException(diagnostics, getMessage(), index);
        tagged.setStackTrace(getStackTrace());
        return tagged;
    }

    private static String format(SourcePos pos, String code, String message) {
        String where = pos == null ? "" : pos + " ";
        String c = code == null ? "" : code + ": ";
        return where + c + message;
    }
}
