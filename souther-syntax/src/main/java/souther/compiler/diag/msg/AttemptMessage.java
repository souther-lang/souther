package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What an attempted construction and the arms answering for it are told. */
public sealed interface AttemptMessage extends Message {

    /** `as` names what a construction builds, and this is not one. */
    @Code(DiagnosticCode.E2012)
    record ThisIsNotAConstruction() implements AttemptMessage {}

    /** What to write instead. */
    @Code(DiagnosticCode.E2012)
    record WriteTheConstructionWhoseInvariantDecides() implements AttemptMessage {}

    /** The type declares no invariant, so the attempt always succeeds. */
    @Code(DiagnosticCode.E2013)
    record TheTypeDeclaresNoInvariant(String data) implements AttemptMessage {}

    /** What to write instead. */
    @Code(DiagnosticCode.E2013)
    record ConstructItDirectlyOrGiveItAnInvariant(String data) implements AttemptMessage {}

    /** The arms answer clauses, and nothing here is attempted for them to answer for. */
    @Code(DiagnosticCode.E2018)
    record NothingHereIsAttempted() implements AttemptMessage {}

    /** What to write instead. */
    @Code(DiagnosticCode.E2018)
    record AttemptTheConstructionOrGiveTheElseOneValue() implements AttemptMessage {}

    /** One clause is answered by two arms. */
    @Code(DiagnosticCode.E2019)
    record TheClauseIsAnsweredTwice(String clause) implements AttemptMessage {}

    /** An arm names a clause the type does not declare. */
    @Code(DiagnosticCode.E2014)
    record NoClauseOfThatName(String clause, String data) implements AttemptMessage {}

    /** Which clauses can be answered by name. */
    @Code(DiagnosticCode.E2014)
    record TheClausesThatCanBeAnswered(String clauses) implements AttemptMessage {}

    /** Clauses that can fail and have no arm. */
    @Code(DiagnosticCode.E2015)
    record TheseClausesHaveNoArm(String clauses, String data) implements AttemptMessage {}

    /** What to write instead. */
    @Code(DiagnosticCode.E2015)
    record AnswerEachOfThemOrGiveTheElseOneValue() implements AttemptMessage {}

    /** Clauses declared without a name, and nothing answering them. */
    @Code(DiagnosticCode.E2016)
    record UnnamedClausesAreLeftUnanswered(String data) implements AttemptMessage {}

    /** What to write instead. */
    @Code(DiagnosticCode.E2016)
    record AddACatchAllArmOrNameThem() implements AttemptMessage {}

    /** A catch-all arm where every clause is named and answered. */
    @Code(DiagnosticCode.E2017)
    record TheCatchAllArmAnswersNothing(String data) implements AttemptMessage {}

    /** What to do about it. */
    @Code(DiagnosticCode.E2017)
    record DropTheCatchAllArm(String data) implements AttemptMessage {}
}
