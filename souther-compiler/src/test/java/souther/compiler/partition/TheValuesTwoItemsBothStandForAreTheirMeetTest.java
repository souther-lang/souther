package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Crossing two items answers about a value exactly where both of them do.
 *
 * <p>Asked of the values and never of the runs. An item is a union, so what two of them share is
 * not a run of either and is not read off their ends: the item a rule singles a value out of is two
 * runs, and crossing it with a run that holds the value yields the parts on both sides of the hole.
 * A reader that took the ends of the first run it found would have the hole back.
 *
 * <p>Membership is the whole of what the answer promises, and this asks it of every case: both
 * ends, the values outside, and the one taken out. What the answer is written as — how many runs,
 * in what order, joined or not — is not asked here, because it is not something the answer says.
 */
class TheValuesTwoItemsBothStandForAreTheirMeetTest {

    private static final Carrier DECIMALS = new Carrier.Dense();

    /** A level of the order those runs are on. */
    private static Level at(String value) {
        return new Level.OnACarrier(DECIMALS, new Count(new BigDecimal(value)));
    }

    /** The run from {@code low} to {@code high}, both ends held. */
    private static LevelRegion from(String low, String high) {
        return LevelRegion.of(new LevelInterval(Bound.at(at(low), true), Bound.at(at(high), true)));
    }

    /** Two runs that overlap share the run between the tighter of each end. */
    @Test
    void twoRunsShareWhatLiesInBoth() {
        LevelRegion both = from("0", "10").meet(from("5", "20"));

        assertTrue(both.contains(at("5")), "the tighter lower end is held");
        assertTrue(both.contains(at("10")), "and so is the tighter upper end");
        assertTrue(both.contains(at("7")), "with what lies between them");
        assertFalse(both.contains(at("4")), "what only the first holds is not in both");
        assertFalse(both.contains(at("11")), "and neither is what only the second holds");
    }

    /** Two runs that do not overlap share nothing, which is the item nothing stands at. */
    @Test
    void twoRunsThatDoNotOverlapShareNothing() {
        LevelRegion both = from("0", "4").meet(from("5", "20"));

        assertEquals(List.of(), both.parts(),
                "runs whose ends cross hold nothing and are not written down");
        assertFalse(both.contains(at("4")), "so nothing of either is in the answer");
        assertFalse(both.contains(at("5")), "from either side of where they pass");
    }

    /**
     * A run crossed with an item a value was taken out of keeps the hole.
     *
     * <p>Which is the case the point of a border asks for: the run it lies in, less the value
     * against the line. Crossed as a pair of ends, the value against the line comes back.
     */
    @Test
    void crossingAnItemWithAHoleKeepsTheHole() {
        LevelRegion both = from("0", "10").meet(from("0", "20").without(at("5")));

        assertTrue(both.contains(at("4")), "what lies under the hole is held");
        assertTrue(both.contains(at("6")), "and so is what lies over it");
        assertFalse(both.contains(at("5")), "and the value taken out is not");
        assertFalse(both.contains(at("11")), "with the narrower run's end still holding");
    }

    /** Two items of several runs each are crossed over every pair of them. */
    @Test
    void everyPairOfRunsIsCrossed() {
        LevelRegion both = from("0", "20").without(at("10"))
                .meet(from("0", "20").without(at("5")));

        assertTrue(both.contains(at("2")), "what lies under both holes is held");
        assertTrue(both.contains(at("7")), "and what lies between them");
        assertTrue(both.contains(at("15")), "and what lies over both");
        assertFalse(both.contains(at("5")), "each hole is taken out of the answer");
        assertFalse(both.contains(at("10")), "whichever item it came from");
    }

    /** An item of one value is held where the other item holds that value, and is otherwise empty. */
    @Test
    void oneValueIsHeldWhereTheOtherItemHoldsIt() {
        LevelRegion inside = LevelRegion.point(at("5")).meet(from("0", "10"));
        LevelRegion outside = LevelRegion.point(at("50")).meet(from("0", "10"));

        assertTrue(inside.contains(at("5")), "the value both stand at is in the answer");
        assertFalse(inside.contains(at("6")), "and nothing beside it is");
        assertEquals(List.of(), outside.parts(),
                "a value the other item does not hold leaves nothing");
    }

    /** Crossing with every value the order has answers about the same values as before. */
    @Test
    void crossingWithEverythingAnswersTheSame() {
        LevelRegion run = from("0", "10").without(at("5"));
        LevelRegion both = run.meet(LevelRegion.EVERYTHING);

        for (String value : List.of("0", "4", "5", "6", "10", "11")) {
            assertEquals(run.contains(at(value)), both.contains(at(value)),
                    () -> "crossing with everything holds what it held at " + value);
        }
    }
}
