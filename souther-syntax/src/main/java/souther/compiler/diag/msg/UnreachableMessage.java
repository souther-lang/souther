package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What an `unreachable` is told about the case it declares cannot arrive. */
public sealed interface UnreachableMessage extends Message {

    /** The model's own rules leave the case standing, so a caller can supply one. */
    @Code(DiagnosticCode.E1326)
    record TheModelAdmitsThisCase(String caseName, String position) implements UnreachableMessage,
            Reported {}

    /** Which declaration says the case can arrive. */
    record ItIsACaseOf(String caseName, String type) implements UnreachableMessage, Supporting {}

    /** What to do instead, in the words the specification uses. */
    record AnswerAValueOrChangeTheInput() implements UnreachableMessage, Supporting {}
}
