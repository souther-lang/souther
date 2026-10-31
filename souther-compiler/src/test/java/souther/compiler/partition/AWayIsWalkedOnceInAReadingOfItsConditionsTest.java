package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A reading of a body walks each way it asks to have walked once ({@link OneReading}): a way built
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

    /** A walk, a new one each time it is walked, counting how often that is. What it comes to is
     *  nothing here: what is asked is whether it is walked. */
    private static final class Walking
            implements Supplier<OneOfEach.Walked<OnTheWay, Reachability>> {

        private int times;

        @Override
        public OneOfEach.Walked<OnTheWay, Reachability> get() {
            times++;
            return new OneOfEach.Walked.Stopped<>(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT);
        }
    }

    @Test
    void theSameConditionsAreWalkedOnceAndHandedTheWalk() {
        List<OnTheWay> conditions = conditions();
        Walking walking = new Walking();
        OneReading.over(() -> {
            OneOfEach.Walked<OnTheWay, Reachability> first =
                    OneReading.walked(conditions, walking);
            assertSame(first, OneReading.walked(new ArrayList<>(conditions), walking),
                    "the same conditions in another list");
            return null;
        });
        assertEquals(1, walking.times, "walked once");
    }

    /** The way asks it for itself: a way built again from the same conditions is handed the walk
     *  the first was. */
    @Test
    void aWayBuiltAgainIsHandedTheWalk() {
        List<OnTheWay> conditions = conditions();
        OneReading.over(() -> {
            assertSame(new WayToTheBorder(conditions).along(),
                    new WayToTheBorder(new ArrayList<>(conditions)).along());
            return null;
        });
    }

    /** And what is handed back is what a walk outside any reading comes to. */
    @Test
    void theWalkHandedBackIsTheWalkOfTheConditions() {
        List<OnTheWay> conditions = conditions();
        OneOfEach.Walked<OnTheWay, Reachability> alone = new WayToTheBorder(conditions).along();
        OneOfEach.Walked<OnTheWay, Reachability> read = OneReading.over(() -> {
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
        Walking walkingOne = new Walking();
        Walking walkingOther = new Walking();
        OneReading.over(() -> {
            OneReading.walked(one, walkingOne);
            OneReading.walked(other, walkingOther);
            return null;
        });
        assertEquals(1, walkingOne.times);
        assertEquals(1, walkingOther.times, "each walked");
    }

    /** And the way of the others names their own entries, which is why they are walked apart. */
    @Test
    void theWayOfConditionsEqualToOthersNamesItsOwnEntries() {
        List<OnTheWay> one = List.of(truth("a", true), truth("c", true));
        List<OnTheWay> other = List.of(truth("a", true), truth("c", true));
        OneReading.over(() -> {
            new WayToTheBorder(one).along();
            OneOfEach.Walked<OnTheWay, Reachability> walked = new WayToTheBorder(other).along();
            if (!(walked instanceof OneOfEach.Walked.Open<OnTheWay, Reachability>(var ways, var _))
                    || !(ways.getFirst() instanceof OneOfEach.Way.Chosen<OnTheWay>(
                            var entries, var _))) {
                return fail("one way open: " + walked);
            }
            assertSame(other.getFirst(), entries.getFirst());
            return null;
        });
    }

    @Test
    void theSameConditionsInAnotherOrderAreAnotherWay() {
        List<OnTheWay> conditions = conditions();
        Walking walking = new Walking();
        Walking turning = new Walking();
        OneReading.over(() -> {
            OneReading.walked(conditions, walking);
            OneReading.walked(conditions.reversed(), turning);
            return null;
        });
        assertEquals(1, turning.times, "walked for itself");
        assertNotEquals(new WayToTheBorder(conditions).along(),
                new WayToTheBorder(conditions.reversed()).along(),
                "whose ways list the conditions in its order");
    }

    /** Outside a reading nothing is kept: each way asked for is walked. */
    @Test
    void outsideAReadingEveryWayIsWalked() {
        List<OnTheWay> conditions = conditions();
        Walking walking = new Walking();
        assertNotSame(OneReading.walked(conditions, walking),
                OneReading.walked(conditions, walking));
        assertEquals(2, walking.times);
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
        OneReading.over(() -> {
            OneOfEach.Walked<OnTheWay, Reachability> first = new WayToTheBorder(conditions).along();
            assertTrue(first instanceof OneOfEach.Walked.Open<OnTheWay, Reachability>(var _,
                            var stoppedBy) && stoppedBy != null,
                    () -> "more ways than are looked along: " + first);
            assertSame(first, new WayToTheBorder(conditions).along());
            return null;
        });
    }
}
