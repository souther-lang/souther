package souther.compiler.cst;

import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.msg.Reported;
import souther.compiler.diag.msg.MessageCodes;

/**
 * A syntax problem recorded during lexing or parsing, positioned by absolute offset so it does not
 * depend on a {@link LineIndex} yet. A driver turns it into a
 * {@link souther.compiler.diag.Diagnostic} once the line index is known.
 *
 * <p>{@code said} is the message, which carries both the values the reader is shown and the rule
 * they look up. Which part of the language did not read is a property of what is being read and not
 * of the token that was missing — a {@code let} written with an empty parameter list and a type
 * variable written outside the core are both refused while parsing, and they are not one rule — so
 * the message the site says is what decides it.
 */
public record CstError(int offset, int width, Reported said) {

    public CstError {
        java.util.Objects.requireNonNull(said, "a syntax error says what did not read");
    }

    /** The rule the text broke. */
    public DiagnosticCode code() {
        return MessageCodes.of(said);
    }

    public static CstError of(int offset, int width, Reported said) {
        return new CstError(offset, width, said);
    }
}
