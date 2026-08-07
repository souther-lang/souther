package souther.compiler.cst;

import souther.compiler.diag.DiagnosticCode;

/**
 * A syntax problem recorded during lexing or parsing, positioned by absolute offset so it does not
 * depend on a {@link LineIndex} yet. A driver turns it into a
 * {@link souther.compiler.diag.Diagnostic} once the line index is known.
 *
 * <p>{@code code} is the rule the text broke and {@code messageKey}/{@code args} feed the localized
 * catalog; {@code legacyMessage} preserves the English text the pre-CST throw sites produced, so
 * existing callers and tests see the same {@code getMessage()}.
 *
 * <p>The code is recorded here rather than decided by the driver because what a reader is told to
 * look up is a property of what they wrote — a `+let+` written with an empty parameter list and a
 * type variable written outside the core are both refused while parsing, and they are not one rule.
 */
public record CstError(int offset, int width, DiagnosticCode code, String messageKey,
                       String legacyMessage, Object[] args) {

    public static CstError of(int offset, int width, DiagnosticCode code, String messageKey,
                              String legacyMessage, Object... args) {
        return new CstError(offset, width, code, messageKey, legacyMessage, args);
    }
}
