package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What an attempted construction and the arms answering for it are told. */
public sealed interface AttemptMessage extends Message {

    /** `as` names what a construction builds, and this is not one. */
    @Code(DiagnosticCode.E2012)
    record ThisIsNotAConstruction() implements AttemptMessage, Reported {}

    /** What to write instead. */
    record WriteTheConstructionWhoseInvariantDecides() implements AttemptMessage {}

    /** The type declares no invariant, so the attempt always succeeds. */
    @Code(DiagnosticCode.E2013)
    record TheTypeDeclaresNoInvariant(String data) implements AttemptMessage, Reported {}

    /** What to write instead. */
    record ConstructItDirectlyOrGiveItAnInvariant(String data) implements AttemptMessage {}

    /** The arms answer clauses, and nothing here is attempted for them to answer for. */
    @Code(DiagnosticCode.E2018)
    record NothingHereIsAttempted() implements AttemptMessage, Reported {}

    /** What to write instead. */
    record AttemptTheConstructionOrGiveTheElseOneValue() implements AttemptMessage {}

    /** One clause is answered by two arms. */
    @Code(DiagnosticCode.E2019)
    record TheClauseIsAnsweredTwice(String clause) implements AttemptMessage, Reported {}

    /** An arm names a clause the type does not declare. */
    @Code(DiagnosticCode.E2014)
    record NoClauseOfThatName(String clause, String data) implements AttemptMessage, Reported {}

    /** Which clauses can be answered by name. */
    record TheClausesThatCanBeAnswered(String clauses) implements AttemptMessage {}

    /** Clauses that can fail and have no arm. */
    @Code(DiagnosticCode.E2015)
    record TheseClausesHaveNoArm(String clauses, String data) implements AttemptMessage, Reported {}

    /** What to write instead. */
    record AnswerEachOfThemOrGiveTheElseOneValue() implements AttemptMessage {}

    /** Clauses declared without a name, and nothing answering them. */
    @Code(DiagnosticCode.E2016)
    record UnnamedClausesAreLeftUnanswered(String data) implements AttemptMessage, Reported {}

    /** What to write instead. */
    record AddACatchAllArmOrNameThem() implements AttemptMessage {}

    /** A catch-all arm where every clause is named and answered. */
    @Code(DiagnosticCode.E2017)
    record TheCatchAllArmAnswersNothing(String data) implements AttemptMessage, Reported {}

    /** What to do about it. */
    record DropTheCatchAllArm(String data) implements AttemptMessage {}
}
