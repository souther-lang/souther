package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a construction is told about the invariant of the type it builds. */
public sealed interface InvariantMessage extends Message {

    /**
     * The guards do not establish a clause, so the construction may abort.
     *
     * <p>{@code unsettled} is the clauses it could not establish. Which clause it is, is what an
     * author acts on: the invariant is the conjunction of its clauses, and being told that "its
     * invariant" may be violated where four of five are settled leaves them to find the fifth by
     * writing one guard at a time.
     *
     * <p>One of four spellings, over two questions a construction answers separately: whether a
     * clause the guards left standing can be named, and whether one they established can be. A
     * spelling carries the names it is written around and no empty ones — a message with a list in
     * it is the message chosen where there is a list, so nothing here renders as punctuation with
     * nothing in front of it.
     */
    @Code(DiagnosticCode.E2011)
    record TheGuardsDoNotEstablish(String data, String unsettled)
            implements InvariantMessage, Reported {}

    /** The same, where the guards did establish clauses that can be named: {@code settled}. */
    @Code(DiagnosticCode.E2011)
    record TheGuardsDoNotEstablishButDoEstablish(String data, String unsettled, String settled)
            implements InvariantMessage, Reported {}

    /** The same, where every clause the check could not establish was written without a name. */
    @Code(DiagnosticCode.E2011)
    record TheGuardsDoNotEstablishTheInvariant(String data) implements InvariantMessage, Reported {}

    /**
     * The same, where the guards did establish clauses that can be named.
     *
     * <p>What the reader is told about is what was established, which is worth saying whether or not
     * the clause left standing beside it was given a name. Said with the invariant unnamed because
     * the two are separate questions: an unnamed clause the guards did not establish does not take
     * the established ones out of the warning with it.
     */
    @Code(DiagnosticCode.E2011)
    record TheGuardsDoNotEstablishTheInvariantButDoEstablish(String data, String settled)
            implements InvariantMessage, Reported {}

    /** What to write where a relation between inputs is what guarantees the clause. */
    record ReifyTheRelationOntoAnInput(String data) implements InvariantMessage, Supporting {}

    /**
     * A clause the guards did not establish, said at the clause.
     *
     * <p>What E2011 points at. It says no more than that, because the clauses it is written over are
     * the ones nothing here established: some of them the values may fail, and some of them are
     * clauses this check simply could not decide. A label claiming more would be untrue of the
     * second kind.
     *
     * <p>Nothing here names the clause. What the label is written beside is the clause, which a
     * reader is being shown; naming it as well would be the diagnostic saying the same thing twice
     * in the one place a reader does not need it said.
     */
    record ThisClauseIsNotEstablishedHere() implements InvariantMessage, Supporting {}

    /**
     * A clause the value being built fails, said at the clause.
     *
     * <p>What E2010 points at, and stronger than the label above because the clauses it is written
     * over are stronger: E2010 is raised on a refutation, and what it is given is the clauses that
     * were refuted rather than every clause left standing beside them.
     */
    record ThisClauseRejectsThisValue() implements InvariantMessage, Supporting {}

    /**
     * A clause a path reaching this construction fails, where the paths fail different clauses.
     *
     * <p>What E2010 points at when no one clause is failed on every path. The invariant is refused
     * whichever way the value comes, which is what the error says; which clause refuses it depends
     * on the path, so saying of any of them that the value fails it would be untrue of the value
     * that comes down the other.
     */
    record ThisClauseRejectsTheValueOnSomeOfThePathsHere()
            implements InvariantMessage, Supporting {}

    /** The value being built is one the invariant rejects, whatever the path. */
    @Code(DiagnosticCode.E2010)
    record TheValueIsOneTheInvariantRejects(String data, String unsettled)
            implements InvariantMessage, Reported {}

    /** The same, where no clause the check refuted was written with a name. */
    @Code(DiagnosticCode.E2010)
    record TheValueIsOneTheInvariantRejectsUnnamed(String data) implements InvariantMessage, Reported {}

    /** The value is rejected under what is assumed where the construction stands. */
    @Code(DiagnosticCode.E2010)
    record TheValueIsRejectedOnAReachablePath(String data, String unsettled)
            implements InvariantMessage, Reported {}

    /** The same, where no clause the check refuted was written with a name. */
    @Code(DiagnosticCode.E2010)
    record TheValueIsRejectedOnAReachablePathUnnamed(String data) implements InvariantMessage, Reported {}

    /** An invariant reaches a helper that carries no termination guarantee. */
    @Code(DiagnosticCode.E1106)
    record TheInvariantReachesAPartialHelper(String data, String partial, String through)
            implements InvariantMessage, Reported {}

    @Code(DiagnosticCode.E1105)
    record TheInvariantConstructsAData(String data, String constructs) implements InvariantMessage, Reported {}

    @Code(DiagnosticCode.E1105)
    record TheNamedClauseConstructsAData(String data, String constructs, String clause) implements InvariantMessage, Reported {}

    record TheClauseReachesThatConstruction(String clause)
            implements InvariantMessage, FindingRegion {}

    record ThisClauseReachesThatConstruction() implements InvariantMessage, FindingRegion {}

    @Code(DiagnosticCode.E1103)
    record TwoClausesShareOneName(String clause, String data) implements InvariantMessage, Reported {}

    @Code(DiagnosticCode.E1102)
    record AUnitDataHasNothingToObserve(String data) implements InvariantMessage, Reported {}

    /**
     * A clause declared on a sum, which nothing constructs.
     *
     * <p>Said where the clause still exists. A sum is lowered into a declaration with no slot for
     * one, so carrying on from here drops the clause and everything written inside it — a call to a
     * function that does not exist compiles clean. What it costs is not one silent clause: a reading
     * that asks which rules are written about a position answers from the declaration, so a rule
     * that never arrived reads as a rule nobody wrote, and a report goes on to say the model draws
     * no distinction there.
     */
    @Code(DiagnosticCode.E1107)
    record ASumIsNeverConstructed(String data) implements InvariantMessage, Reported {}

    /** Where the same rule is written instead: on the case that is built, or on a newtype over the
     *  sum, which is built and carries its own check. */
    record WriteItOnACaseOrOnANewtypeOverTheSum(String data)
            implements InvariantMessage, Supporting {}

    @Code(DiagnosticCode.E1104)
    record UnderscoreCannotNameAClause(String data) implements InvariantMessage, Reported {}

    record NameTheClauseOrLeaveItUnnamed() implements InvariantMessage, Supporting {}

    @Code(DiagnosticCode.E1106)
    record AnInvariantAnswersOnEveryPath(String data) implements InvariantMessage, Reported {}
}
