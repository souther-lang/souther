package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;

/**
 * What a reading of a rule recorded about the line it drew.
 *
 * <p>The classification the rule already has ({@link ComparisonClaim}), carried to whoever reads the
 * line. A rule either orders the values either side of what it names or names one value and orders
 * nothing, and the two say different things about their own line: an order says which side the value
 * it wrote belongs to, and a rule that names a value has no side to answer with. Opened into a
 * boolean apiece, the second has to answer the first's question anyway, and what it answers is
 * invented — so a reader asking which way such a rule is satisfied is given a side about a line that
 * has none, and reads it.
 *
 * <p>Worked out once from what the producer knows, and never worked back out of what came later. A
 * bound records which way it keeps its values and whether it admits the value it stops at, and which
 * side of the line that value is on follows from the two — so it is settled here, beside the rule
 * that knows both, rather than by a consumer holding the range every rule together left. A bound is
 * an order: it keeps a run of the values, and that nothing outside it can be constructed is a fact
 * about the construct rather than about what its comparison placed.
 *
 * <p>And what a border <em>makes</em> of this — which way the rule is satisfied from its line, which
 * points a row is owed at, which of the four each of them is — is {@link Border}'s, derived there
 * from this and derived nowhere else. A reading says what it read, and a measure says what that
 * means for the rows it asks for.
 *
 * @param claim what the rule placed on the values: an order either side of the value it wrote, or
 *              that value singled out from every other one
 */
public record LineFacts(ComparisonClaim claim) {

    /**
     * The line a rule that keeps a run of the values drew, which is what a bound is.
     *
     * <p>The one place a caller holding an order as two facts rather than as the claim can make one
     * of these. A bound keeps the values one way of its own and admits its own value or does not,
     * and those are the two an order is; a rule that names a value has neither, so there is no way
     * in here to ask for one and no way to build the state where a value both is named and belongs
     * to a side.
     */
    public static LineFacts ordering(boolean valueBelongsBelow, boolean holdsAtTheValue) {
        return new LineFacts(new ComparisonClaim.Cut(valueBelongsBelow, holdsAtTheValue));
    }

    /**
     * Whether the rule is true at the line's own value, which is what says which of the two points
     * against the line a row there stands at.
     *
     * <p>Asked of either shape, because either answers it: {@code x <= c} and {@code x > c} agree
     * about which class the value is in and disagree here, and {@code x == c} is met at the value
     * where {@code x /= c} is not.
     */
    public boolean holdsAtTheValue() {
        return claim.holdsAtTheValue();
    }

    /** Whether the rule names a value rather than ordering the values either side of it. */
    public boolean singles() {
        return claim instanceof ComparisonClaim.Singled;
    }

    /**
     * Whether a row at one point of this line satisfies the rule that drew it.
     *
     * <p>The half of the role that is the rule's, where the other half is the place's
     * ({@link DomainPoint#againstTheLine}). One derivation, because two things ask it: a border
     * classifying its own points, and a debt saying which of the four it is without a border in
     * hand. Written twice, the two would answer differently for whichever shape of line was added
     * next.
     *
     * <p>A point beside the line is a point exactly because the values there fall in another class
     * than the line's own value, so the rule answers there opposite to how it answers at the line. A
     * run is in the class the rule is satisfied in on the side it is satisfied on; a rule that names
     * a value is satisfied at no run at all where it is satisfied at the value, since what it is
     * satisfied by is that value and nothing else.
     */
    public boolean holdsAt(DomainPoint point) {
        return switch (point) {
            case DomainPoint.AtTheLine _ -> holdsAtTheValue();
            case DomainPoint.BesideTheLine _ -> !holdsAtTheValue();
            case DomainPoint.InTheRegion in -> claim instanceof ComparisonClaim.Cut order
                    ? in.side() == Border.satisfyingSide(order.holdsAtTheValue(),
                            order.valueBelongsBelow())
                    : !holdsAtTheValue();
        };
    }
}
