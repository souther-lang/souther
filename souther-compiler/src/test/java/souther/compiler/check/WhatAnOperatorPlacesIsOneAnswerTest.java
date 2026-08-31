package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.types.BinOp;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The algebra of what an operator places, which is what lets a reader stop holding the operator.
 *
 * <p>Three laws, and each of them is what some reading rests on. That the classification and
 * {@link BinOp#compares} agree is what makes a claim the evidence that an operator compares. That
 * turning a statement round twice is the statement is what lets a reading turn one round wherever
 * it meets it. And that classifying the operator a swap would have been written with is the same as
 * turning the classification round is what lets a reader swap the sides without an operator table
 * of its own — the table a reading of a body's comparisons used to hold.
 */
class WhatAnOperatorPlacesIsOneAnswerTest {

    /** The operator each one states when its two operands change places. Written out here and
     *  nowhere in the compiler: what a reading does with a swap is turn the claim round, and this
     *  is the table that says the two are one. */
    private static final Map<BinOp, BinOp> SWAPPED = swapped();

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
}
