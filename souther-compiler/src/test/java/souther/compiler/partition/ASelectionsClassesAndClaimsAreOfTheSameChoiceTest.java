package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.coverage.Observation;

import java.util.List;
import java.util.OptionalInt;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination's classes and its claims are two halves of one choice.
 *
 * <p>Which combination of a group is being asked for is an index counted off the ways of settling
 * each factor. Both halves are read off that index — which classes are left open, and what a run
 * that settled the factors those ways would be seen to have done — so the two are the same choice
 * only for as long as they are counted off the same way. Read apart they would agree for a group of
 * one factor, agree for a square group by luck, and part on the first group whose factors have
 * different numbers of ways.
 *
 * <p>Built here rather than read off a model. A group of two factors with different widths and
 * choices that leave a position nothing is a shape a model in the corpus need not have, and a
 * mechanism is untested for shapes its data never takes.
 */
class ASelectionsClassesAndClaimsAreOfTheSameChoiceTest {

    /** One position with four classes; nothing said about it yet. */
    private static InteractionCells.Cell holding(int... classes) {
        boolean[] allowed = new boolean[4];
        for (int each : classes) {
            allowed[each] = true;
        }
        return new InteractionCells.Cell(new boolean[][] {allowed});
    }

    /** A place a run can be recorded at, told from its neighbours by the probe it carries. */
    private static ControlClaim at(int probe) {
        return ControlClaim.of(new ControlPointId.ArmOccurrence(probe, OptionalInt.of(probe),
                        null, null))
                .orElseThrow(() -> new AssertionError("an arm with a probe can be claimed"));
    }

    private static Observation lit(int... probes) {
        java.util.Set<Integer> taken = new java.util.LinkedHashSet<>();
        for (int each : probes) {
            taken.add(each);
        }
        return new Observation(taken, java.util.Set.of());
    }

    /**
     * Every combination's claims are the claims of the ways it settles the factors.
     *
     * <p>The factors have three ways and two, so an index read off them in a different order picks a
     * different pair — which is what makes the classes that survive say which pair was picked. Each
     * of the six is checked, so a swap that happens to be its own inverse for one of them does not
     * pass.
     */
    @Test
    void aCombinationsClaimsAreOfTheWaysItsClassesCameFrom() {
        InteractionCells.Group group = new InteractionCells.Group(
                new InteractionCells.Placed(holding(0, 1, 2, 3), List.of(at(9))),
                List.of(
                        List.of(new InteractionCells.Placed(holding(0, 1), List.of(at(10))),
                                new InteractionCells.Placed(holding(2), List.of(at(11))),
                                new InteractionCells.Placed(holding(3), List.of(at(12)))),
                        List.of(new InteractionCells.Placed(holding(0, 2, 3), List.of(at(20))),
                                new InteractionCells.Placed(holding(1, 2, 3), List.of(at(21))))));

        assertEquals(6, group.size(), "three ways and two ways");
        List<List<Integer>> byIndex = List.of(
                List.of(0, 9, 10, 20), List.of(2, 9, 11, 20), List.of(3, 9, 12, 20),
                List.of(1, 9, 10, 21), List.of(2, 9, 11, 21), List.of(3, 9, 12, 21));
        for (int index = 0; index < byIndex.size(); index++) {
            CellSelection selection = group.at(index);
            List<Integer> expected = byIndex.get(index);
            assertTrue(selection.cell().admits(0, expected.get(0)),
                    "combination " + index + " leaves the class its two ways share");
            assertEquals(expected.subList(1, expected.size()).stream().map(
                            ASelectionsClassesAndClaimsAreOfTheSameChoiceTest::at).toList(),
                    selection.claims(),
                    "and claims the way in and the two ways it settles the factors");
        }
    }

    /** A choice whose ways leave the position nothing is not a combination, and carries no claim. */
    @Test
    void aChoiceWithNothingLeftIsNotACombination() {
        InteractionCells.Group group = new InteractionCells.Group(
                new InteractionCells.Placed(holding(0, 1, 2, 3), List.of()),
                List.of(
                        List.of(new InteractionCells.Placed(holding(0), List.of(at(10))),
                                new InteractionCells.Placed(holding(1), List.of(at(11)))),
                        List.of(new InteractionCells.Placed(holding(0), List.of(at(20))),
                                new InteractionCells.Placed(holding(1), List.of(at(21))))));

        assertEquals(2, group.left(0), "two of the four choices are combinations");
        assertNull(group.at(1), "the first way of one factor and the second of the other agree "
                + "on nothing");
        assertNull(group.at(2), "nor the other way round");
    }

    /**
     * A witness is made out of a run, and out of nothing else.
     *
     * <p>What a witness says is that this row filled this combination, which is the one conclusion
     * here a reader may act on. A caller holding the classes a row sits in cannot reach for one, so
     * the reading that composed a row cannot come back as evidence for itself.
     */
    @Test
    void aWitnessIsMadeOnlyFromARunThatDidWhatTheCombinationNames() {
        InteractionCells.Group group = new InteractionCells.Group(
                new InteractionCells.Placed(holding(0, 1, 2, 3), List.of(at(9))),
                List.of(List.of(new InteractionCells.Placed(holding(0, 1), List.of(at(10))),
                        new InteractionCells.Placed(holding(2, 3), List.of(at(11))))));
        CellSelection selection = group.at(0);
        int[] where = {0};

        assertTrue(selection.certifying(where, lit(9, 10)).isPresent(),
                "a run that did both makes one");
        assertTrue(selection.certifying(where, lit(9, 11)).isEmpty(),
                "a run that settled the factor the other way makes none");
        assertTrue(selection.certifying(where, lit(10)).isEmpty(),
                "nor one that never took the way in");
        assertEquals(selection,
                selection.certifying(where, lit(9, 10)).orElseThrow().of(),
                "and the one it makes says which combination it filled");
    }

    /**
     * A combination is certified by a run that did everything it names, and by nothing less.
     *
     * <p>What is missing is answered rather than only whether anything is: a row that did not take
     * the way in and a row that took it and settled a factor the other way are two different things
     * to be told, and a reading that answered `no` to both would send the same sentence for each.
     */
    @Test
    void aCombinationIsCertifiedByARunThatDidEverythingItNames() {
        InteractionCells.Group group = new InteractionCells.Group(
                new InteractionCells.Placed(holding(0, 1, 2, 3), List.of(at(9))),
                List.of(List.of(new InteractionCells.Placed(holding(0, 1), List.of(at(10))),
                        new InteractionCells.Placed(holding(2, 3), List.of(at(11))))));
        CellSelection selection = group.at(0);

        assertTrue(selection.certifiedBy(lit(9, 10)), "a run that did both did this combination");
        assertEquals(List.of(at(10)), selection.missedBy(lit(9, 11)),
                "a run that reached the meeting and settled the factor the other way missed that");
        assertEquals(List.of(at(9)), selection.missedBy(lit(10)),
                "and one that settled the factor without taking the way in missed the way in");
        assertFalse(selection.certifiedBy(lit(9)), "neither of which certifies it");
    }
}
