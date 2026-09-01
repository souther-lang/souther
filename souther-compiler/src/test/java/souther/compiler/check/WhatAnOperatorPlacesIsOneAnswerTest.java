package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.Towards;
import souther.compiler.types.BinOp;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The algebra of what an operator places, which is what lets a reader stop holding the operator.
 *
 * <p>Each law is what some reading rests on. That the classification and {@link BinOp#compares}
 * agree is what makes a claim the evidence that an operator compares. That turning a statement
 * round twice is the statement is what lets a reading turn one round wherever it meets it. That
 * classifying the operator a swap would have been written with is the same as turning the
 * classification round is what lets a reader swap the sides without an operator table of its own,
 * and the same holds of a denial — a rule met under a negation states the comparison that holds
 * where it does not, and asking which operator that would have been is a second table.
 *
 * <p>And the two facts a cut holds are put together in one place, so the side a rule is satisfied
 * on is one answer however many readings want it. Turning a comparison round moves it and denying
 * one moves it, which is the whole of what the two operations do to a line.
 */
class WhatAnOperatorPlacesIsOneAnswerTest {

    /** The operator each one states when its two operands change places. Written out here and
     *  nowhere in the compiler: what a reading does with a swap is turn the claim round, and this
     *  is the table that says the two are one. */
    private static final Map<BinOp, BinOp> SWAPPED = swapped();

    /** The operator each one states the failure of. Written out here and nowhere in the compiler:
     *  what a reading does with a negation is deny the claim, and this is the table that says the
     *  two are one. */
    private static final Map<BinOp, BinOp> DENIED = denied();

    /** Which side of its own line each order is true on. The four cases of the one derivation from
     *  the two facts a cut holds. */
    private static final Map<BinOp, Towards> SATISFIED_ON = satisfiedOn();

    private static Map<BinOp, BinOp> swapped() {
        Map<BinOp, BinOp> pairs = new LinkedHashMap<>();
        pairs.put(BinOp.LT, BinOp.GT);
        pairs.put(BinOp.GT, BinOp.LT);
        pairs.put(BinOp.LE, BinOp.GE);
        pairs.put(BinOp.GE, BinOp.LE);
        pairs.put(BinOp.EQ, BinOp.EQ);
        pairs.put(BinOp.NE, BinOp.NE);
        return pairs;
    }

    private static Map<BinOp, BinOp> denied() {
        Map<BinOp, BinOp> pairs = new LinkedHashMap<>();
        pairs.put(BinOp.LT, BinOp.GE);
        pairs.put(BinOp.GE, BinOp.LT);
        pairs.put(BinOp.LE, BinOp.GT);
        pairs.put(BinOp.GT, BinOp.LE);
        pairs.put(BinOp.EQ, BinOp.NE);
        pairs.put(BinOp.NE, BinOp.EQ);
        return pairs;
    }

    private static Map<BinOp, Towards> satisfiedOn() {
        Map<BinOp, Towards> sides = new LinkedHashMap<>();
        sides.put(BinOp.LT, Towards.BELOW);
        sides.put(BinOp.LE, Towards.BELOW);
        sides.put(BinOp.GT, Towards.ABOVE);
        sides.put(BinOp.GE, Towards.ABOVE);
        return sides;
    }

    /** What an operator places is a claim exactly where the operator compares. Two spellings of one
     *  membership drift, and an operator added to the language would land in them differently. */
    @Test
    void whatPlacesSomethingIsWhatCompares() {
        Map<BinOp, Boolean> places = new LinkedHashMap<>();
        Map<BinOp, Boolean> compares = new LinkedHashMap<>();
        for (BinOp op : BinOp.values()) {
            places.put(op, ComparisonPlacement.of(op) instanceof ComparisonClaim);
            compares.put(op, op.compares());
        }
        assertEquals(compares, places,
                "what an operator places and whether it compares are one question");
    }

    /** Turning a statement round twice is the statement. Asked of every operator and not of the
     *  comparisons alone, because it is the wide answer a reader of any binary turns round. */
    @Test
    void turningAPlacementRoundTwiceLeavesIt() {
        for (BinOp op : BinOp.values()) {
            ComparisonPlacement placed = ComparisonPlacement.of(op);
            assertEquals(placed, placed.turned().turned(),
                    () -> "turning " + op + " round twice states what it stated");
        }
    }

    /**
     * Reading the swapped operator and turning the reading round come to the same claim.
     *
     * <p>What a reader of a comparison written the other way round rests on. Where the two part, a
     * reading that swaps the sides and turns the claim round says something the source did not, and
     * the only way to notice is to write the operator table again beside it.
     */
    @Test
    void swappingTheSidesIsTurningWhatWasPlaced() {
        for (Map.Entry<BinOp, BinOp> each : SWAPPED.entrySet()) {
            assertEquals(ComparisonPlacement.of(each.getValue()),
                    ComparisonPlacement.of(each.getKey()).turned(),
                    () -> "what " + each.getKey() + " places, turned round, is what "
                            + each.getValue() + " places");
        }
    }

    /** An operator that places nothing has nothing to turn round, which is what lets a reading of
     *  any binary turn one round before it knows whether it is a comparison. */
    @Test
    void anOperatorThatPlacesNothingTurnsIntoItself() {
        for (BinOp op : BinOp.values()) {
            if (op.compares()) {
                continue;
            }
            ComparisonPlacement placed = ComparisonPlacement.of(op);
            assertEquals(placed, placed.turned(),
                    () -> op + " places nothing, and nothing turned round is nothing");
        }
    }

    /**
     * Reading the operator that holds where one does not and denying the reading come to the same
     * claim.
     *
     * <p>What a reading meeting a rule under a negation rests on. Where the two part, a reading
     * that denies the claim states a rule the source did not, and the way it was noticed before was
     * to write the operator table again beside it.
     */
    @Test
    void denyingAComparisonIsReadingTheOneThatHoldsWhereItDoesNot() {
        for (Map.Entry<BinOp, BinOp> each : DENIED.entrySet()) {
            assertEquals(ComparisonPlacement.of(each.getValue()),
                    claim(each.getKey()).denied(),
                    () -> "what " + each.getKey() + " places, denied, is what "
                            + each.getValue() + " places");
        }
    }

    /** Denying a claim twice is the claim, which is what lets a reading deny one wherever it meets
     *  a negation rather than counting how many it is under. */
    @Test
    void denyingAClaimTwiceLeavesIt() {
        for (BinOp op : DENIED.keySet()) {
            assertEquals(claim(op), claim(op).denied().denied(),
                    () -> "denying " + op + " twice states what it stated");
        }
    }

    /** Turning a claim round and denying it are done in either order, which is what lets a reading
     *  do them as it meets them rather than in an order it has to keep. */
    @Test
    void turningAndDenyingAreDoneInEitherOrder() {
        for (BinOp op : DENIED.keySet()) {
            assertEquals(claim(op).turned().denied(), claim(op).denied().turned(),
                    () -> "turning " + op + " round and denying it, either way about");
        }
    }

    /**
     * Which side each order is satisfied on, written out so that the four are the specification.
     *
     * <p>The one derivation from the two facts a cut holds. Every reading that wants the side asks
     * this, and the table is here rather than in any of them.
     */
    @Test
    void anOrderIsSatisfiedOnTheSideItsOwnValueDecides() {
        Map<BinOp, Towards> sides = new LinkedHashMap<>();
        for (BinOp op : SATISFIED_ON.keySet()) {
            sides.put(op, cut(op).satisfyingSide());
        }
        assertEquals(SATISFIED_ON, sides,
                "which side of its line each order is true on");
    }

    /** Turning an order round moves the side it is satisfied on, and so does denying it. Both move
     *  it, so a reading that does one of them and keeps the side it had is a reading whose line has
     *  its sides the wrong way round. */
    @Test
    void turningAndDenyingBothMoveTheSatisfyingSide() {
        for (BinOp op : SATISFIED_ON.keySet()) {
            Towards side = cut(op).satisfyingSide();
            assertEquals(side.opposite(), cut(op).turned().satisfyingSide(),
                    () -> op + " turned round is satisfied on the other side");
            assertEquals(side.opposite(), cut(op).denied().satisfyingSide(),
                    () -> op + " denied is satisfied on the other side");
        }
    }

    /** An order built from the side it is satisfied on is the order that side was read off, which
     *  is what a reader holding the end a bound kept rather than the class its value is in rests
     *  on. */
    @Test
    void anOrderIsWhatItsSatisfyingSideBuildsBack() {
        for (BinOp op : SATISFIED_ON.keySet()) {
            ComparisonClaim.Cut cut = cut(op);
            assertEquals(cut,
                    ComparisonClaim.Cut.satisfiedOn(cut.satisfyingSide(), cut.holdsAtTheValue()),
                    () -> op + " read as a side and built back from it");
        }
    }

    private static ComparisonClaim claim(BinOp op) {
        return assertInstanceOf(ComparisonClaim.class, ComparisonPlacement.of(op),
                () -> op + " compares its two sides, so it placed something");
    }

    private static ComparisonClaim.Cut cut(BinOp op) {
        return assertInstanceOf(ComparisonClaim.Cut.class, ComparisonPlacement.of(op),
                () -> op + " orders the values either side of what it names");
    }
}
