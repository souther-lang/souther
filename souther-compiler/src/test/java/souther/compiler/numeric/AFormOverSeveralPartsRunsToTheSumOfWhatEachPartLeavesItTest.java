package souther.compiler.numeric;

import souther.compiler.numeric.NumericDomain.Bounds;

import org.junit.jupiter.api.Test;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A form over positions of several parts lies where the sum of what each part leaves its own
 * positions does.
 *
 * <p>Parts share no position and no rule, so each reaches its greatest whatever the others do. A
 * query may take one rule as a premise ({@link FormReach}); asked of the parts together, a sum of
 * three amounts that a rule bounds in pairs would take the rule of one pair and the ends of the
 * rest, and the rules of the other pairs would bound nothing.
 */
class AFormOverSeveralPartsRunsToTheSumOfWhatEachPartLeavesItTest {

    private static LinearForm<String> atom(String a) {
        return LinearForm.<String>atom(a);
    }

    private static LinearForm<String> num(long n) {
        return LinearForm.<String>constant(ExactRatio.of(n));
    }

    private static Map<String, NumberSpace> whole(String... atoms) {
        Map<String, NumberSpace> out = new LinkedHashMap<>();
        for (String each : atoms) {
            out.put(each, NumberSpace.spacedOnly(Granularity.DISCRETE));
        }
        return out;
    }

    /** {@code x, y >= 0} with {@code x + y <= 10}, and {@code u, v >= 0}, whose sum {@code rule}
     *  bounds if it is given. */
    private static NumericDomain<String> twoPairs(boolean ruleOnTheSecond) {
        Map<String, NumberSpace> spaces = whole("x", "y", "u", "v");
        NumericDomain<String> d = NumericDomain.top(CanonicalOrder.asTheyAreSpelled(),
                        ClosedStates.kept())
                .assume(atom("x"), Rel.GE, spaces)
                .assume(atom("y"), Rel.GE, spaces)
                .assume(atom("u"), Rel.GE, spaces)
                .assume(atom("v"), Rel.GE, spaces)
                .assume(atom("u").minus(num(10)), Rel.LE, spaces)
                .assume(atom("v").minus(num(10)), Rel.LE, spaces)
                .assume(LinearForm.sumOfAtoms("x", "y").minus(num(10)), Rel.LE, spaces);
        return ruleOnTheSecond
                ? d.assume(LinearForm.sumOfAtoms("u", "v").minus(num(10)), Rel.LE, spaces)
                : d;
    }

    private static LinearForm<String> sumOfAll() {
        return LinearForm.sumOfAtoms("x", "y").plus(LinearForm.sumOfAtoms("u", "v")).orNull();
    }

    /** Each pair is held by a rule of its own, and the rule of one is not spent on the other. */
    @Test
    void aRuleOfEachPartBoundsThePositionsOfThatPart() {
        Bounds bounds = twoPairs(true).boundsOf(sumOfAll());

        assertEquals(Endpoint.inclusive(Count.of(0)), bounds.min());
        assertEquals(Endpoint.inclusive(Count.of(20)), bounds.max());
    }

    /** Control: the second pair has only the ends of its positions, which give twenty. */
    @Test
    void aPartWithNoRuleOfItsOwnIsBoundedByItsEndsAlone() {
        Bounds bounds = twoPairs(false).boundsOf(sumOfAll());

        assertEquals(Endpoint.inclusive(Count.of(30)), bounds.max());
    }

    /** A form weighing one part against another lies where the least of one meets the greatest of
     *  the other. */
    @Test
    void aDifferenceOfPartsLiesBetweenTheEndsOfTheirSums() {
        LinearForm<String> difference =
                LinearForm.sumOfAtoms("x", "y").minus(LinearForm.sumOfAtoms("u", "v")).orNull();

        Bounds bounds = twoPairs(true).boundsOf(difference);

        assertEquals(Endpoint.inclusive(Count.of(-10)), bounds.min());
        assertEquals(Endpoint.inclusive(Count.of(10)), bounds.max());
    }
}
