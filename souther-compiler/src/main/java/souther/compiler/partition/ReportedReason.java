package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;

/**
 * The word an adequacy document writes for a reason a derivation stopped.
 *
 * <p>Between the two vocabularies and belonging to neither. {@link BlockReason} records what this
 * compiler could not do and does not know how it is reported; {@link UndividedPosition.Reason} is
 * what a document promises its reader they can tell apart and does not know what produced it. A
 * projection owned by either would be that one reaching into the other, which is the direction the
 * split was made to stop.
 *
 * <p>So a second surface — a diagnostic that says more than the document does — is another
 * projection beside this one rather than a change to what a reason is.
 */
public final class ReportedReason {

    /**
     * Deliberately coarser than what it is given. What a reader of a document is promised is which
     * kind of thing stopped the derivation, not which capability this compiler is missing this
     * month: three missing traversals are one word, because the model reads the same whichever of
     * them it was.
     *
     * <p>One switch rather than an answer on each case, because a coarsening is only reviewable
     * where the collapses are visible together. No {@code default}, so a reason added and not said
     * stops the compile rather than arriving in a report as the nearest word that already existed.
     */
    public static UndividedPosition.Reason of(BlockReason reason) {
        return switch (reason) {
            case BlockReason.RuleAboutADerivedValue _ ->
                    UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE;
            case BlockReason.TypeUnresolved _ -> UndividedPosition.Reason.TYPE_UNRESOLVED;
            case BlockReason.DepthLimit _ -> UndividedPosition.Reason.DEPTH_LIMIT;
            case BlockReason.UnsupportedTraversal _ ->
                    UndividedPosition.Reason.UNSUPPORTED_TRAVERSAL;
            case BlockReason.UnreadComparisonForm _ ->
                    UndividedPosition.Reason.UNSUPPORTED_SYNTAX;
            case BlockReason.UnreadValueRule _ -> UndividedPosition.Reason.UNSUPPORTED_SYNTAX;
            // Its own word, and not the one above. Both are rules this reading did not turn into a
            // line, and a reader acting on them is doing different work: one wants a reader for a
            // form that was seen, and one wants the gathering to reach the rules at all. Collapsed
            // together, a position whose rules nothing had looked at was reported as an expression
            // the terms do not name, which is a cause it was never observed to have.
            case BlockReason.ValueRulesNotReached _ ->
                    UndividedPosition.Reason.RULES_NOT_READ_AT_ALL;
            case BlockReason.UnreadComparisonDomain _ ->
                    UndividedPosition.Reason.UNSUPPORTED_DOMAIN;
            case BlockReason.CompetingCoordinates _ ->
                    UndividedPosition.Reason.COMPETING_COORDINATES;
            // Its own word, and not the shape one below. Both sides of this line are read and
            // ordered and a line is drawn on them; what is missing is which positions the line runs
            // between, which is a question about the model and not about the form it was written in.
            case BlockReason.CasePairingNotDetermined _ ->
                    UndividedPosition.Reason.UNRESOLVED_CASE_PAIRING;
            case BlockReason.ComparisonBetweenPositions _ ->
                    UndividedPosition.Reason.UNSUPPORTED_PARTITION_SHAPE;
            // The same word, from the other reading of the same rule. What a document promises its
            // reader is which kind of thing stopped the derivation, and a relation between two
            // positions is one kind of thing whether the reading that met it was drawing a line or
            // gathering values — so the split this compiler needs between the two is a split it
            // keeps to itself, and the two vocabularies still come to one word for one rule.
            case BlockReason.ValueRuleRelatingTwoPositions _ ->
                    UndividedPosition.Reason.UNSUPPORTED_PARTITION_SHAPE;
            // Its own word and not the one above. Both are rules this read to the end that divide
            // nothing, and what a reader may go on to do about them differs: one is waiting on a
            // class about two positions, and the other has nothing to wait for.
            case BlockReason.ComparisonCuttingNothing _ ->
                    UndividedPosition.Reason.RULE_CUTS_NOTHING;
            // And its own word beside that one. A rule with no quantity to cut states nothing about
            // the position; a rule whose line falls outside where its quantity runs states
            // something no row satisfies, and an author reading the first would take the second for
            // a clause they could delete.
            case BlockReason.ComparisonCuttingOutsideDomain _ ->
                    UndividedPosition.Reason.RULE_CUTS_OUTSIDE_WHAT_THE_QUANTITY_HOLDS;
        };
    }

    private ReportedReason() {}
}
