package souther.compiler.partition;

import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.ArmProbe;
import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.Numberings;
import souther.compiler.coverage.Runs;
import souther.compiler.coverage.SiteNumbering;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination's classes, its claims and the decisions it is are all read off one choice.
 *
 * <p>Which combination of a group is being asked for is an index counted off the ways of settling
 * each factor. All three are read off that index — which classes are left open, what a run that
 * settled the factors those ways would be seen to have done, and which decisions of the model that
 * is — so they are the same choice only for as long as they are counted off the same way. Read
 * apart they would agree for a group of one factor, agree for a square group by luck, and part on
 * the first group whose factors have different numbers of ways.
 *
 * <p>Built here rather than read off a model. A group of two factors with different widths and
 * choices that leave a position nothing is a shape a model in the corpus need not have, and a
 * mechanism is untested for shapes its data never takes.
 */
class AChoicesClassesClaimsAndDecisionsAreAllOfThatChoiceTest {

    /** One position with four classes; nothing said about it yet. */
    private static InteractionCells.Cell holding(int... classes) {
        boolean[] allowed = new boolean[4];
        for (int each : classes) {
            allowed[each] = true;
        }
        return new InteractionCells.Cell(new boolean[][] {allowed});
    }

    /** One way of settling something: the classes it leaves, the place a run that took it is
     *  recorded at, and the decision that is. One number for all three, so that a fixture naming
     *  it names one way. */
    private static InteractionCells.Placed placed(InteractionCells.Cell cell, int probe) {
        return new InteractionCells.Placed(cell, List.of(at(probe)), settling(probe));
    }

    /** What a run that passed the place at {@code probe} settled, in the model's words. Beside
     *  {@link #at}, so that a fixture naming one number names one decision both ways. */
    private static List<souther.compiler.reading.Condition> settling(int probe) {
        return List.of(new souther.compiler.reading.Condition.Arm(
                Numberings.armOfForkAt(probe)));
    }

    /** The numbering this fixture's places are of. One of them, so that two places written here as
     *  the same number are the same place. */
    private static final SiteNumbering NUMBERING = Numberings.ofArms(32);

    private static ArmProbe probe(int raw) {
        return NUMBERING.arm(raw);
    }

    /** A place a run can be recorded at, told from its neighbours by the probe it carries. */
    private static ControlClaim at(int probe) {
        return ControlClaim.of(new ControlPlace.Arm(Numberings.armOfForkAt(probe),
                        java.util.Optional.of(probe(probe)), null))
                .orElseThrow(() -> new AssertionError("an arm with a probe can be claimed"));
    }

    /** A run read as having been at those places of this fixture's numbering. */
    private static AlignedObservation lit(int... probes) {
        Set<ArmProbe> arms = new LinkedHashSet<>();
        for (int each : probes) {
            arms.add(probe(each));
        }
        return Runs.at(NUMBERING, arms);
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
                placed(holding(0, 1, 2, 3), 9),
                List.of(
                        List.of(placed(holding(0, 1), 10), placed(holding(2), 11),
                                placed(holding(3), 12)),
                        List.of(placed(holding(0, 2, 3), 20), placed(holding(1, 2, 3), 21))));

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
                            AChoicesClassesClaimsAndDecisionsAreAllOfThatChoiceTest::at).toList(),
                    selection.claims(),
                    "and claims the way in and the two ways it settles the factors");
        }
    }

    /**
     * And the decisions it is are the decisions of those same ways.
     *
     * <p>What a combination is asked for by is the decisions; where a row for it is looked for is
     * the classes. Counted off the index apart, the two would name different choices of the same
     * group — and what a run was held to would be the decisions of one combination while the
     * requirement it answered was named after another.
     *
     * <p>Over all six, and against the ways rather than against the claims: the claims are the
     * other half of this law, and a reading that took its decisions off them would pass by saying
     * nothing.
     */
    @Test
    void aCombinationsDecisionsAreOfTheWaysItsClassesCameFrom() {
        InteractionCells.Group group = new InteractionCells.Group(
                placed(holding(0, 1, 2, 3), 9),
                List.of(
                        List.of(placed(holding(0, 1), 10), placed(holding(2), 11),
                                placed(holding(3), 12)),
                        List.of(placed(holding(0, 2, 3), 20), placed(holding(1, 2, 3), 21))));

        List<List<Integer>> byIndex = List.of(
                List.of(9, 10, 20), List.of(9, 11, 20), List.of(9, 12, 20),
                List.of(9, 10, 21), List.of(9, 11, 21), List.of(9, 12, 21));
        for (int index = 0; index < byIndex.size(); index++) {
            Set<souther.compiler.reading.Condition> expected = new LinkedHashSet<>();
            byIndex.get(index).forEach(each -> expected.addAll(settling(each)));
            assertEquals(expected, group.settledAt(index),
                    "combination " + index + " is the way in and the two ways it settles the"
                            + " factors");
        }
    }

    /** A choice the classes leave nothing at is no combination to be named either. */
    @Test
    void aChoiceThatIsNotACombinationIsNoRequirement() {
        InteractionCells.Group group = new InteractionCells.Group(
                placed(holding(0, 1, 2, 3), 9),
                List.of(List.of(placed(holding(0), 10), placed(holding(1), 11)),
                        List.of(placed(holding(0), 20), placed(holding(1), 21))));

        assertNull(group.at(1), "the two ways agree on nothing");
        assertNull(group.settledAt(1), "so there is nothing there to ask a row for");
        assertEquals(Set.of(new souther.compiler.reading.Condition.Arm(
                        Numberings.armOfForkAt(9)),
                        new souther.compiler.reading.Condition.Arm(Numberings.armOfForkAt(10)),
                        new souther.compiler.reading.Condition.Arm(Numberings.armOfForkAt(20))),
                group.settledAt(0),
                "while the choice they do agree on is one");
    }

    /** A choice whose ways leave the position nothing is not a combination, and carries no claim. */
    @Test
    void aChoiceWithNothingLeftIsNotACombination() {
        InteractionCells.Group group = new InteractionCells.Group(
                new InteractionCells.Placed(holding(0, 1, 2, 3), List.of(), List.of()),
                List.of(
                        List.of(placed(holding(0), 10), placed(holding(1), 11)),
                        List.of(placed(holding(0), 20), placed(holding(1), 21))));

        assertEquals(2, group.left(0), "two of the four choices are combinations");
        assertNull(group.at(1), "the first way of one factor and the second of the other agree "
                + "on nothing");
        assertNull(group.at(2), "nor the other way round");
    }

    /**
     * A witness takes both halves: the row sits where the combination leaves room, and the run did
     * what it names.
     *
     * <p>Either alone is a different statement. A run that did everything the combination names,
     * paired with a row sitting somewhere the combination excludes, is a witness that some row
     * filled it and not that this one did — and the value would be handed on to a reader who cannot
     * tell the difference.
     */
    @Test
    void aWitnessIsOfARowTheCombinationLeavesRoomFor() {
        InteractionCells.Group group = new InteractionCells.Group(
                placed(holding(0, 1, 2, 3), 9),
                List.of(List.of(placed(holding(0, 1), 10), placed(holding(2, 3), 11))));
        CellSelection selection = group.at(0);

        assertTrue(selection.certifying(new int[] {1}, lit(9, 10)).isPresent(),
                "a row the combination leaves room for, seen doing what it names");
        assertTrue(selection.certifying(new int[] {2}, lit(9, 10)).isEmpty(),
                "and one sitting where it leaves none is no witness, whatever the run did");
    }

    /**
     * A combination of decisions is something a run can be held to.
     *
     * <p>Allowed to claim nothing, it would be a combination every run certifies — including one
     * that did nothing at all. A claim dropped by whatever reads the body would then come back not
     * as a combination nothing can witness, which is loud, but as one everything does, which is
     * silent and wrong.
     */
    @Test
    void aCombinationClaimingNothingIsNotOne() {
        assertThrows(IllegalArgumentException.class,
                () -> new CellSelection(holding(0, 1), List.of()));
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
                placed(holding(0, 1, 2, 3), 9),
                List.of(List.of(placed(holding(0, 1), 10), placed(holding(2, 3), 11))));
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
                placed(holding(0, 1, 2, 3), 9),
                List.of(List.of(placed(holding(0, 1), 10), placed(holding(2, 3), 11))));
        CellSelection selection = group.at(0);

        assertTrue(selection.certifiedBy(lit(9, 10)), "a run that did both did this combination");
        assertEquals(List.of(at(10)), selection.missedBy(lit(9, 11)),
                "a run that reached the meeting and settled the factor the other way missed that");
        assertEquals(List.of(at(9)), selection.missedBy(lit(10)),
                "and one that settled the factor without taking the way in missed the way in");
        assertFalse(selection.certifiedBy(lit(9)), "neither of which certifies it");
    }
}
