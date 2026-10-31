package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A reading of a body walks each way it asks to have walked once ({@link WaysWalked}): a way built
 * again from the same conditions, in the same order, is handed the walk already walked, and what
 * comes back is that walk and not one like it.
 *
 * <p>The same conditions, each by identity, and nothing less: the ways a walk hands on name the
 * choices they made by the entries they were made at, so a way of other conditions, however
 * alike, is walked for itself.
 */
class AWayIsWalkedOnceInAReadingOfItsConditionsTest {

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0));

    private static OnTheWay truth(String name, boolean held) {
        return new OnTheWay.TakenIn(WHERE, new RowDemand.ATruth(TermPath.of("r").then(name), held));
    }

    /** {@code a || b} beside {@code c}, each entry made afresh. */
    private static List<OnTheWay> conditions() {
        return List.of(OnTheWay.OneOf.of(new ConditionOccurrence("f",
                        ConditionOccurrence.Reading.DECIDING, 1), WHERE,
                        List.of(List.of(truth("a", true)), List.of(truth("b", true))),
                        Optional.empty()),
                truth("c", true));
    }

    @Test
    void theSameConditionsAreWalkedOnceAndHandedTheWalk() {
        List<OnTheWay> conditions = conditions();
        WaysWalked.over(() -> {
            OneOfEach.Walked<OnTheWay, Reachability> first =
                    new WayToTheBorder(conditions).along();
            OneOfEach.Walked<OnTheWay, Reachability> again =
                    new WayToTheBorder(new ArrayList<>(conditions)).along();
            assertSame(first, again, "a way built again from the same conditions");
            assertEquals(1, WaysWalked.walkedSoFar(), "and walked once");
            return null;
        });
    }

    /** And what is handed back is what a walk outside any reading comes to. */
    @Test
    void theWalkHandedBackIsTheWalkOfTheConditions() {
        List<OnTheWay> conditions = conditions();
        OneOfEach.Walked<OnTheWay, Reachability> alone = new WayToTheBorder(conditions).along();
        OneOfEach.Walked<OnTheWay, Reachability> read = WaysWalked.over(() -> {
            new WayToTheBorder(conditions).along();
            return new WayToTheBorder(conditions).along();
        });
        assertEquals(alone, read);
    }

    @Test
    void conditionsEqualToThemButOthersAreWalkedForThemselves() {
        List<OnTheWay> one = List.of(truth("a", true), truth("c", true));
        List<OnTheWay> other = List.of(truth("a", true), truth("c", true));
        assertEquals(one, other, "alike");
        WaysWalked.over(() -> {
            new WayToTheBorder(one).along();
            OneOfEach.Walked<OnTheWay, Reachability> walked = new WayToTheBorder(other).along();
            assertEquals(2, WaysWalked.walkedSoFar(), "each walked");
            if (!(walked instanceof OneOfEach.Walked.Open<OnTheWay, Reachability>(var ways, var _))
                    || !(ways.getFirst() instanceof OneOfEach.Way.Chosen<OnTheWay>(
                            var entries, var _))) {
                return fail("one way open: " + walked);
            }
            assertSame(other.getFirst(), entries.getFirst(),
                    "and the way names the asker's own entries");
            return null;
        });
    }

    @Test
    void theSameConditionsInAnotherOrderAreAnotherWay() {
        List<OnTheWay> conditions = conditions();
        WaysWalked.over(() -> {
            OneOfEach.Walked<OnTheWay, Reachability> first =
                    new WayToTheBorder(conditions).along();
            OneOfEach.Walked<OnTheWay, Reachability> turned =
                    new WayToTheBorder(conditions.reversed()).along();
            assertEquals(2, WaysWalked.walkedSoFar());
            assertNotEquals(first, turned, "whose ways list the conditions in its order");
            return null;
        });
    }

    /** Outside a reading nothing is kept: each way asked for is walked. */
    @Test
    void outsideAReadingEveryWayIsWalked() {
        List<OnTheWay> conditions = conditions();
        OneOfEach.Walked<OnTheWay, Reachability> first = new WayToTheBorder(conditions).along();
        OneOfEach.Walked<OnTheWay, Reachability> again = new WayToTheBorder(conditions).along();
        assertNotSame(first, again);
        assertEquals(first, again);
        assertEquals(0, WaysWalked.walkedSoFar());
    }

    /** A walk the figure stopped is handed back stopped, by the same figure. */
    @Test
    void aWalkPastAFigureIsHandedBackWithTheFigure() {
        List<OnTheWay> conditions = new ArrayList<>();
        for (int each = 0; each < 5; each++) {
            conditions.add(OnTheWay.OneOf.of(new ConditionOccurrence("f",
                            ConditionOccurrence.Reading.DECIDING, 10 + each), WHERE,
                    List.of(List.of(truth("p" + each, true)), List.of(truth("p" + each, false))),
                    Optional.empty()));
        }
        WaysWalked.over(() -> {
            OneOfEach.Walked<OnTheWay, Reachability> first = new WayToTheBorder(conditions).along();
            assertTrue(first instanceof OneOfEach.Walked.Open<OnTheWay, Reachability>(var _,
                            var stoppedBy) && stoppedBy != null,
                    () -> "more ways than are looked along: " + first);
            assertSame(first, new WayToTheBorder(conditions).along());
            return null;
        });
    }
}
