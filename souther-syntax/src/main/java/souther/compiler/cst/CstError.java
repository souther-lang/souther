package souther.compiler.cst;

import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.MessageCodes;
import souther.compiler.diag.msg.Reported;

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
 *
 * <p>Carried as a type variable rather than as a {@code Message} because what it holds is what a
 * diagnostic will be about, and a driver has to be able to say so: a hint is a message too, and one
 * that reached here would be a syntax error reported under whatever code nothing gave it. Read as
 * {@code CstError<?>}, which hands a driver back a value that is both.
 */
public record CstError<M extends Message & Reported>(int offset, int width, M said) {

    public CstError {
        java.util.Objects.requireNonNull(said, "a syntax error says what did not read");
    }

    /** The rule the text broke. */
    public DiagnosticCode code() {
        return MessageCodes.of(said);
    }

    public static <M extends Message & Reported> CstError<M> of(int offset, int width, M said) {
        return new CstError<>(offset, width, said);
    }
}
