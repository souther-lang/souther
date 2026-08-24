package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPointId;

import java.util.List;
import java.util.Map;
import java.util.OptionalInt;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many things a combination can be asking, and what each of them says.
 *
 * <p>A combination is a class apiece at the positions it is about. Where it leaves one of them more
 * than one class it is asking more than one thing, and a search bounded at three tries should get
 * three of those.
 *
 * <p>What it used to get was three assignments. An assignment fixes every position — the ones the
 * combination is about and the ones it says nothing about alike — and the ones it says nothing about
 * are the search's own choice. Counted off together, the first three assignments of a combination
 * over one free position of four classes were one thing asked four ways, and the second thing the
 * combination could have been asking went untried however much of the bound was left.
 *
 * <p>Built here rather than read off a model. A combination that leaves two positions open beside a
 * free one is a shape a model in the corpus need not have, and a mechanism is untested for shapes
 * its data never takes.
 */
class WhatACombinationAsksIsItsOwnToSayTest {

    /** Four classes at each position, with the ones listed left open. */
    private static boolean[] leaving(int... classes) {
        boolean[] allowed = new boolean[4];
        for (int each : classes) {
            allowed[each] = true;
        }
        return allowed;
    }

    private static CellSelection over(boolean[]... positions) {
        return new CellSelection(new InteractionCells.Cell(positions),
                List.of(ControlClaim.of(new ControlPointId.ArmOccurrence(1, OptionalInt.of(1),
                                null, null))
                        .orElseThrow(() -> new AssertionError("an arm with a probe can be claimed"))));
    }

    /**
     * A reading says where the positions the combination is about stand, and says nothing anywhere
     * else.
     */
    @Test
    void aReadingIsAboutThePositionsTheCombinationNarrows() {
        CellSelection selection =
                over(leaving(0, 1, 2, 3), leaving(0, 2), leaving(1));

        assertEquals(List.of(Map.of(1, 0, 2, 1), Map.of(1, 2, 2, 1)),
                selection.interpretations(8).stream().map(Interpretation::pins).toList(),
                "the free position is no part of what the combination asks");
    }

    /**
     * A position the combination says nothing about does not multiply what it is asking.
     *
     * <p>Which is the whole of what the bound is for. The two things this combination can be asking
     * are both within three tries; counted over assignments, the first three were one of them at
     * three of the free position's four classes.
     */
    @Test
    void aFreePositionDoesNotMultiplyTheReadings() {
        CellSelection selection =
                over(leaving(0, 1, 2, 3), leaving(0, 2), leaving(1));

        assertEquals(2, selection.interpretations(3).size(),
                "two things asked, whatever the free position may hold");
        assertTrue(selection.interpretations(3).stream()
                        .allMatch(reading -> reading.at().equals(java.util.Set.of(1, 2))),
                "and both of them are about the same two positions");
    }

    /**
     * A position with nothing left at it is no combination, and is not a reading that failed.
     *
     * <p>Told apart because they are different news. A combination the model does not have is not
     * one a search came back empty from, and the second sends a person looking for values to write.
     */
    @Test
    void aPositionWithNothingLeftAtItIsNoCombination() {
        assertEquals(List.of(), over(leaving(0, 1, 2, 3), leaving()).interpretations(3),
                "nothing stands at the second position, so there is nothing to look for");
    }
}
