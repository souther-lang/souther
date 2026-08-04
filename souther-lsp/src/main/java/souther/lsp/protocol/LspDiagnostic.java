package souther.lsp.protocol;

import java.util.List;

/**
 * An LSP diagnostic: a range, a severity (1 = error, 2 = warning, 3 = information, 4 = hint), a
 * stable code (the compiler's {@code E1301}-style identifier, or {@code null}), the message, and the
 * other places the same problem points at.
 *
 * <p>{@code related} is what the compiler's secondary regions become: the operands of a failed
 * comparison, the earlier of two imports, or — when the problem is written in two files — the half
 * that is not in this one. An editor lists them under the diagnostic and lets a reader jump to each.
 *
 * <p>{@code tags} says what kind of thing this is over and above its severity. The one that matters
 * here is {@link #UNNECESSARY}: an editor fades the range rather than only listing the diagnostic,
 * which is how a reader sees at a glance that the text does nothing.
 */
public record LspDiagnostic(Range range, int severity, String code, String message,
                            List<Integer> tags, List<Related> related) {

    public static final int ERROR = 1;
    public static final int WARNING = 2;
    public static final int INFORMATION = 3;
    public static final int HINT = 4;

    /** Text that is there and does nothing. An editor renders the range faded. */
    public static final int UNNECESSARY = 1;

    /** One other place a diagnostic points at: where it is, and what it says about it. */
    public record Related(String uri, Range range, String message) {}

    public LspDiagnostic {
        tags = tags == null ? List.of() : List.copyOf(tags);
        related = related == null ? List.of() : List.copyOf(related);
    }

    /** A diagnostic with nothing to say about itself beyond where it is and what it says. */
    public LspDiagnostic(Range range, int severity, String code, String message,
                         List<Related> related) {
        this(range, severity, code, message, List.of(), related);
    }

    /** A diagnostic that points at one place only. */
    public LspDiagnostic(Range range, int severity, String code, String message) {
        this(range, severity, code, message, List.of(), List.of());
    }
}
