package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;

/**
 * A side of a border, away from the line: what an {@code IN} or an {@code OUT} point is a row in.
 *
 * <p>A set and not a value. Which values are in it is the whole of what it says, and the value this
 * or that search happens to compose inside it is a witness rather than the item — a row anywhere in
 * the region is at the point, and a reader holding a representative instead would call every other
 * row in it uncovered. So the representative is asked of this ({@link #standingIn}) and is no part of
 * what one region is: two searches that composed different values inside one region found the same
 * coverage item.
 *
 * <p>Two shapes, both of them about places at one term. A line between two positions has sides too,
 * and they are not sets of one position's values — a row is in one of them by writing two places
 * that stand in the right order — so they are said as a criterion over the pair
 * ({@link Criterion.WhereTheTermsAreFurtherApartThan}) rather than as a region here.
 */
public sealed interface Region {

    /** Which way along the order a region runs from where it starts. */
    enum Towards {
        ABOVE,
        BELOW
    }

    /**
     * Every place strictly past {@code from}, the way {@code towards} says.
     *
     * <p>What both sides of a border at a place are. The {@code IN} region starts at the {@code ON}
     * point and runs inwards; the {@code OUT} region starts at the {@code OFF} point and runs
     * outwards. Where the point it would start at is one the carrier names no value for, it starts at
     * the line itself — the values one step away are not there to be excluded, and everything past
     * the line on that side is as far from the border as anything gets.
     */
    record Beyond(Place from, Towards towards) implements Region {

        @Override
        public boolean holds(Place at) {
            int order = at.compareTo(from);
            return towards == Towards.ABOVE ? order > 0 : order < 0;
        }

        /**
         * Where this region stops on the low side, which is its own end or the position's, whichever
         * is tighter.
         *
         * <p>Both, and not the region's alone. A region running above a place is bounded below by
         * that place and above by wherever the position stops, and a reader that took only the first
         * would find every upward region inhabited however narrow the rules had left the position.
         */
        Endpoint low(NumericDomain.Bounds within) {
            return towards == Towards.ABOVE
                    ? Endpoint.lower(Endpoint.exclusive(from), within.min()) : within.min();
        }

        /** The same on the high side. */
        Endpoint high(NumericDomain.Bounds within) {
            return towards == Towards.BELOW
                    ? Endpoint.upper(Endpoint.exclusive(from), within.max()) : within.max();
        }
    }

    /**
     * Every place the position admits other than one.
     *
     * <p>What a border that has no far side leaves. An invariant refuses everything outside its
     * bound, so the side it bounds is the whole of what the position holds; a rule that singles a
     * value out puts every other value in one class, and that class is what lies away from the point.
     * Neither of them is a run of the order from somewhere, which is why it is a shape of its own
     * rather than a {@link Beyond} with an end nobody wrote.
     *
     * <p>Admission is not tested here. What is asked of this is whether a row is in it, and a row's
     * value went through the decoder — so every place a row can hand it is one the rules admit, and
     * the one thing left to ask is whether it is the place against the line.
     */
    record AdmittedOtherThan(Place excluded) implements Region {

        @Override
        public boolean holds(Place at) {
            return !at.sameAs(excluded);
        }
    }

    /**
     * Whether a place is in this region.
     *
     * <p>On the interface because it is what a region is. A value stands for a region only where the
     * region says it is in it, and every shape answers that question — asked of one shape and not
     * another, a witness composed for a side stood for it on the strength of the arithmetic that
     * composed it rather than on the region's own answer.
     */
    boolean holds(Place at);

    /**
     * Whether the rules leave this region no place at all, where that can be settled.
     *
     * <p>A proof and never a search that came up empty. Where the ends are known and have crossed,
     * nothing is there and the point is not one anybody is owed; where they have not, or where one of
     * them was never written down, this answers false and the point stays owed. A region a search
     * could not compose a value in is a different account and is the writability's to give — read as
     * emptiness it would take a coverage item away on the strength of what this compiler can build.
     */
    default boolean provablyHoldsNothing(NumericDomain.Bounds within) {
        return switch (this) {
            case Beyond beyond ->
                    !Endpoint.someValueLiesBetween(beyond.low(within), beyond.high(within));
            // Both ends known, at the one place, and holding it: the position admits that place and
            // nothing else, so there is nothing else for a row to be written at.
            case AdmittedOtherThan other -> within.min() != null && within.max() != null
                    && within.min().inclusive() && within.max().inclusive()
                    && within.min().at().sameAs(other.excluded())
                    && within.max().at().sameAs(other.excluded());
        };
    }

    /**
     * A place inside this region for a search to build a row at, or null where nothing here names
     * one.
     *
     * <p>Asked of the region and held by nobody. Null is "this compiler composed none", which is the
     * account an edge nothing has promised already gets — it is not a claim that the region is empty,
     * and {@link #provablyHoldsNothing} is the only thing that says that.
     *
     * <p>A line between two positions answers with nothing. The place a row writes at both of them is
     * the pair's answer and not one term's, and it is worked out where the pair is.
     */
    default Place standingIn(Carrier carrier, NumericDomain.Bounds within) {
        return held(carrier, switch (this) {
            case Beyond beyond ->
                    carrier.somethingInside(beyond.low(within), beyond.high(within));
            case AdmittedOtherThan other ->
                    carrier.somethingOtherThan(java.util.List.of(other.excluded()), within);
        });
    }

    /**
     * What the carrier offered, once this region has agreed that it is inside.
     *
     * <p>Both shapes, and that is the point of doing it here. Which values a region holds is the
     * region's own answer, and a search that composed one is offering a candidate rather than
     * settling the question — so the offer is put back to the region whichever shape composed it. A
     * region open at one end was offered the count at that very end this way, and a class of
     * everything but one value was offered that value.
     *
     * <p>The grid is asked first and separately. The carrier's spacing says what a value may be
     * sharpened onto and does not promise that every number between two counts is one, which is the
     * carrier's question rather than the region's.
     */
    private Place held(Carrier carrier, Place offered) {
        if (offered == null) {
            return null;
        }
        Place onTheGrid = carrier.onTheGrid(offered);
        return onTheGrid != null && holds(onTheGrid) ? onTheGrid : null;
    }
}
