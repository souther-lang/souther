package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A region says its runs only narrow when a position is fixed for the numbers that was held for, and
 * says no for any other.
 *
 * <p>What {@code ARegionRunsNoWiderOnceMoreIsSaidTest} holds is a list of kinds of number, and the
 * word a region gives has to be as wide as that list and not wider. A kind taken of a position is
 * not the same as another taken of it: the length of a list was held and the length of a string, the
 * sum of a list or a quotient were not. Asked of a number that was not, the region says no, and a
 * search over it is left to the walk.
 */
class ARegionVouchesOnlyForTheNumbersItWasHeldForTest {

    @Test
    void itVouchesForEveryNumberThePropertyIsHeldFor() {
        List<NumericTerm> held = new ArrayList<>();
        for (String name : RegionsRefinedAtRandom.EVERY_NUMBER) {
            held.add(RegionsRefinedAtRandom.anyTerm(name));
        }

        assertTrue(RegionsRefinedAtRandom.region().runsOnlyNarrowWhenFixed(held),
                "the numbers the property test makes: " + held);
        for (NumericTerm each : held) {
            assertTrue(RegionsRefinedAtRandom.region().runsOnlyNarrowWhenFixed(List.of(each)),
                    "one at a time: " + each);
        }
    }

    @Test
    void itDoesNotVouchForAnyOtherNumberTakenOfAPosition() {
        for (NumericTerm each : RegionsRefinedAtRandom.notHeldFor()) {
            assertFalse(RegionsRefinedAtRandom.region().runsOnlyNarrowWhenFixed(List.of(each)),
                    "a number the property was not held for: " + each);
        }
    }

    @Test
    void oneNumberItWasNotHeldForTakesTheWordAwayFromTheRest() {
        List<NumericTerm> beside = new ArrayList<>(List.of(RegionsRefinedAtRandom.term("x"),
                RegionsRefinedAtRandom.anyTerm("x%3")));
        beside.add(RegionsRefinedAtRandom.notHeldFor().getFirst());

        assertFalse(RegionsRefinedAtRandom.region().runsOnlyNarrowWhenFixed(beside));
    }
}
