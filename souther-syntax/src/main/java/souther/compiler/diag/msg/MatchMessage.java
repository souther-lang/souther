package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a `match` and its arms are told. */
public sealed interface MatchMessage extends Message {

    /** The subject is not a sum, so there are no cases to open. */
    @Code(DiagnosticCode.E1202)
    record TheSubjectIsNotASum(String given) implements MatchMessage, Reported {}

    /** An arm names something the subject does not have as a case. */
    @Code(DiagnosticCode.E1203)
    record NotACaseOf(String caseName, String subject) implements MatchMessage, Reported {}

    /** Where the name is a case of another sum, which is the match it belongs to. */
    record ItIsACaseOfAnotherSum(String caseName, String sum) implements MatchMessage {}

    /** Where an inner match swallowed the arms written after it. */
    record AMatchInAnArmTakesTheArmsAfterIt() implements MatchMessage {}

    /** Two arms match one case. */
    @Code(DiagnosticCode.E1204)
    record MatchedByMoreThanOneCase(String caseName) implements MatchMessage, Reported {}

    /** A match with nothing to answer with. */
    @Code(DiagnosticCode.E1205)
    record ThisMatchHasNoCases() implements MatchMessage, Reported {}

    /** An or-pattern in a match over an optional. */
    @Code(DiagnosticCode.E1207)
    record AnOptionMatchTakesNoOrPattern() implements MatchMessage, Reported {}

    /** An arm of a match over an optional names something other than Some or None. */
    @Code(DiagnosticCode.E1203)
    record NotACaseOfAnOptional(String caseName) implements MatchMessage, Reported {}

    /** A case that holds nothing is opened as though it held something. */
    @Code(DiagnosticCode.E1206)
    record TheCaseHasNoValueToOpen(String caseName) implements MatchMessage, Reported {}

    /** A pattern opens a name that is not a newtype. */
    @Code(DiagnosticCode.E1206)
    record NotANewtypeToOpen(String name) implements MatchMessage, Reported {}

    /** What to write to bind the value itself rather than open it. */
    record BindTheMatchedValueInstead(String name) implements MatchMessage {}

    /** A newtype pattern opens a layer of another type than the one it wraps. */
    @Code(DiagnosticCode.E1206)
    record TheNewtypeWrapsAnotherType(String name, String wraps, String opened)
            implements MatchMessage, Reported {}

    /** An or-pattern binds the sum, so it cannot open a case's value. */
    @Code(DiagnosticCode.E1207)
    record AnOrPatternOpensNothing() implements MatchMessage, Reported {}

    /** The arms answer with values of two types. */
    @Code(DiagnosticCode.E1208)
    record TheBranchesDisagree(String one, String other) implements MatchMessage, Reported {}
}
