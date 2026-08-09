package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a construction is told about the invariant of the type it builds. */
public sealed interface InvariantMessage extends Message {

    /**
     * The guards do not establish a clause, so the construction may abort.
     *
     * <p>{@code unsettled} is the clauses it could not establish and {@code settled} the ones it
     * did. Which clause it is, is what an author acts on: the invariant is the conjunction of its
     * clauses, and being told that "its invariant" may be violated where four of five are settled
     * leaves them to find the fifth by writing one guard at a time.
     */
    @Code(DiagnosticCode.E2011)
    record TheGuardsDoNotEstablish(String data, String unsettled, String settled)
            implements InvariantMessage {}

    /** The same, where every clause the check could not establish was written without a name. */
    @Code(DiagnosticCode.E2011)
    record TheGuardsDoNotEstablishTheInvariant(String data) implements InvariantMessage {}

    /** What to write where a relation between inputs is what guarantees the clause. */
    @Code(DiagnosticCode.E2011)
    record ReifyTheRelationOntoAnInput(String data) implements InvariantMessage {}

    /** The value being built is one the invariant rejects, whatever the path. */
    @Code(DiagnosticCode.E2010)
    record TheValueIsOneTheInvariantRejects(String data, String unsettled)
            implements InvariantMessage {}

    /** The same, where no clause the check refuted was written with a name. */
    @Code(DiagnosticCode.E2010)
    record TheValueIsOneTheInvariantRejectsUnnamed(String data) implements InvariantMessage {}

    /** The value is rejected under what is assumed where the construction stands. */
    @Code(DiagnosticCode.E2010)
    record TheValueIsRejectedOnAReachablePath(String data, String unsettled)
            implements InvariantMessage {}

    /** The same, where no clause the check refuted was written with a name. */
    @Code(DiagnosticCode.E2010)
    record TheValueIsRejectedOnAReachablePathUnnamed(String data) implements InvariantMessage {}

    /** An invariant reaches a helper that carries no termination guarantee. */
    @Code(DiagnosticCode.E1106)
    record TheInvariantReachesAPartialHelper(String data, String partial, String through)
            implements InvariantMessage {}

    @Code(DiagnosticCode.E1105)
    record TheInvariantConstructsAData(String data, String constructs) implements InvariantMessage {}

    @Code(DiagnosticCode.E1105)
    record TheNamedClauseConstructsAData(String data, String constructs, String clause) implements InvariantMessage {}

    @Code(DiagnosticCode.E1105)
    record TheClauseReachesThatConstruction(String clause) implements InvariantMessage {}

    @Code(DiagnosticCode.E1105)
    record ThisClauseReachesThatConstruction() implements InvariantMessage {}

    @Code(DiagnosticCode.E1103)
    record TwoClausesShareOneName(String clause, String data) implements InvariantMessage {}

    @Code(DiagnosticCode.E1102)
    record AUnitDataHasNothingToObserve(String data) implements InvariantMessage {}

    @Code(DiagnosticCode.E1104)
    record UnderscoreCannotNameAClause(String data) implements InvariantMessage {}

    @Code(DiagnosticCode.E1104)
    record NameTheClauseOrLeaveItUnnamed() implements InvariantMessage {}

    @Code(DiagnosticCode.E1106)
    record AnInvariantAnswersOnEveryPath(String data) implements InvariantMessage {}
}
