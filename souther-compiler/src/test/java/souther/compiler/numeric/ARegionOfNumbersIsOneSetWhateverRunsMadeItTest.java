package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A region of numbers is the set its runs make together: the same numbers are the same region
 * however they were cut into runs, and two runs with a number between them stay two.
 */
class ARegionOfNumbersIsOneSetWhateverRunsMadeItTest {

    private static ExactCut in(long at) {
        return ExactCut.inclusive(ExactRatio.of(at));
    }

    private static ExactCut below(long at) {
        return ExactCut.exclusive(ExactRatio.of(at));
    }

    private static NumberRegion.Run run(ExactCut from, ExactCut to) {
        return new NumberRegion.Run(from, to);
    }

    @Test
    void runsThatOverlapAreOneRun() {
        assertEquals(NumberRegion.of(List.of(run(in(0), below(10)))),
                NumberRegion.of(List.of(run(in(5), below(10)), run(in(0), below(7)))));
    }

    @Test
    void runsMeetingAtANumberOneOfThemHoldsAreOneRun() {
        assertEquals(NumberRegion.of(List.of(run(in(0), in(10)))),
                NumberRegion.of(List.of(run(in(0), below(5)), run(in(5), in(10)))));
        assertEquals(NumberRegion.of(List.of(run(in(0), in(10)))),
                NumberRegion.of(List.of(run(in(0), in(5)), run(below(5), in(10)))));
    }

    @Test
    void runsMeetingAtANumberNeitherHoldsAreTwoRuns() {
        NumberRegion apart = NumberRegion.of(List.of(run(in(0), below(5)), run(below(5), in(10))));
        assertEquals(2, apart.runs().size());
    }

    @Test
    void aRunWithNoEndsHoldsEveryOther() {
        assertEquals(NumberRegion.of(List.of(run(null, null))),
                NumberRegion.of(List.of(run(in(3), in(4)), run(null, below(3)), run(in(2), null))));
    }

    @Test
    void runsWithANumberBetweenThemKeepTheNumber() {
        NumberRegion both = NumberRegion.of(List.of(run(in(20), null), run(null, below(0))));
        assertEquals(List.of(run(null, below(0)), run(in(20), null)), both.runs());
    }

    @Test
    void aRunHoldsSomeNumber() {
        assertThrows(IllegalArgumentException.class, () -> run(in(5), below(5)));
        assertThrows(IllegalArgumentException.class, () -> run(in(6), in(5)));
        run(in(5), in(5));
    }

    @Test
    void aRegionHoldsSome() {
        assertThrows(IllegalArgumentException.class, () -> NumberRegion.of(List.of()));
    }

    @Test
    void theOrderTellsApartExactlyWhatEqualityDoes() {
        List<NumberRegion> every = List.of(
                NumberRegion.of(List.of(run(null, below(0)))),
                NumberRegion.of(List.of(run(null, in(0)))),
                NumberRegion.of(List.of(run(in(0), null))),
                NumberRegion.of(List.of(run(below(0), null))),
                NumberRegion.of(List.of(run(null, null))),
                NumberRegion.of(List.of(run(null, below(0)), run(in(2), null))),
                NumberRegion.of(List.of(run(in(1), in(3)))));
        for (NumberRegion one : every) {
            for (NumberRegion other : every) {
                assertEquals(one.equals(other), one.compareTo(other) == 0, one + " and " + other);
                assertEquals(Integer.signum(one.compareTo(other)),
                        -Integer.signum(other.compareTo(one)));
            }
        }
        assertTrue(every.stream().sorted().distinct().count() == every.size());
    }
}
