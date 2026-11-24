package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Extreme;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Line;
import souther.compiler.inputs.WhatARelationLeavesUndivided.SettledRun;
import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which places the values that settle a relation leave undivided, asked of the runs and the number
 * they are runs of.
 *
 * <p>A line on a number is drawn as a line on a place only where one place answers the number. And
 * it parts the values of places only where it picks elements out: a count of how often a value
 * occurs does, though no place can be asked for it, so its places are not shown undivided; a line
 * the orders' ends alone draw parts none of them. Each case pairs a number one place answers with
 * ones none does, over the same runs.
 */
class ALineOnANumberIsALineOnAPlaceOnlyWhereItPartsTheValuesOfOneTest {

    private static final TermPath XS = TermPath.of("xs");

    private static final NumericTerm ONE_PLACE = new NumericTerm.ValueOf(TermPath.of("x"));

    /** Read off the elements beside one: no place answers them, and their lines pick elements out. */
    private static final List<NumericTerm> OF_NEIGHBOURS = List.of(
            NumericTerm.Multiplicity.of(XS, XS.element()),
            NumericTerm.ExtremeOfItsKey.of(XS, XS.element().then("account"),
                    XS.element().then("days"), Extreme.LEAST));

    private static final ExactRatio NOUGHT = ExactRatio.of(0);

    /** Settled at nought or below, and not above it: one line. */
    private static Leaves.Settled settledAtNought(List<Line> ofTheTypeAlone) {
        return new Leaves.Settled(List.of(
                new SettledRun(null, ExactCut.inclusive(NOUGHT), true),
                new SettledRun(ExactCut.exclusive(NOUGHT), null, false)), null, null, false,
                ofTheTypeAlone, List.of());
    }

    @Test
    void aLineOnANumberOnePlaceAnswersIsDrawnOnThatPlaceAndLeavesItDivided() {
        Leaves.Settled settled = settledAtNought(List.of());
        assertEquals(List.of(new Line(Rel.LE, NOUGHT)), settled.linesOnAPlaceOf(ONE_PLACE));
        assertFalse(settled.leavesItsPlacesUndivided(ONE_PLACE));
    }

    @Test
    void aLineOnANumberReadOffNeighboursIsDrawnOnNoPlaceAndStillDividesTheElements() {
        Leaves.Settled settled = settledAtNought(List.of());
        for (NumericTerm number : OF_NEIGHBOURS) {
            assertEquals(List.of(new Line(Rel.LE, NOUGHT)), settled.lines());
            assertEquals(List.of(), settled.linesOnAPlaceOf(number), number.toString());
            assertFalse(settled.leavesItsPlacesUndivided(number), number.toString());
        }
    }

    @Test
    void aLineTheOrdersEndsAloneDrawLeavesThePlacesUndividedWhateverTheNumber() {
        Leaves.Settled settled = settledAtNought(List.of(new Line(Rel.LE, NOUGHT)));
        assertEquals(List.of(), settled.linesOnAPlaceOf(ONE_PLACE));
        assertTrue(settled.leavesItsPlacesUndivided(ONE_PLACE));
        for (NumericTerm number : OF_NEIGHBOURS) {
            assertTrue(settled.leavesItsPlacesUndivided(number), number.toString());
        }
        assertTrue(settled.leavesItsPlacesUndivided(null));
    }

    @Test
    void aSideThatIsNoNumberKeepsTheLinesTheModelDraws() {
        Leaves.Settled settled = settledAtNought(List.of());
        assertEquals(List.of(new Line(Rel.LE, NOUGHT)), settled.linesOnAPlaceOf(null));
        assertFalse(settled.leavesItsPlacesUndivided(null));
    }

    @Test
    void aNumberSettledAtEveryValueDrawsNoLineAndLeavesNoPlaceToSayUndividedOf() {
        Leaves.Settled everywhere = new Leaves.Settled(List.of(
                new SettledRun(null, null, true)), null, null, false, List.of(), List.of());
        assertEquals(List.of(), everywhere.lines());
        assertFalse(everywhere.leavesItsPlacesUndivided(ONE_PLACE));
        for (NumericTerm number : OF_NEIGHBOURS) {
            assertFalse(everywhere.leavesItsPlacesUndivided(number), number.toString());
        }
    }

    @Test
    void onlyATotalOfARunPartsNoPlaceByALine() {
        assertFalse(ONE_PLACE.partsNoPlaceByALine());
        for (NumericTerm number : OF_NEIGHBOURS) {
            assertFalse(number.partsNoPlaceByALine(), number.toString());
        }
    }
}
