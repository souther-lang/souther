package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Three readers asked what a weighted sum runs between and three answered it: the algebra summing a
 * goal, the reduction summing the rest of a rule, and the partition layer summing a quantity to see
 * whether a threshold is a value it ever takes.
 *
 * <p>Four lines of arithmetic, two of which are easy to get wrong in ways nothing catches — which
 * end of a position to read, and whether the sum reaches its own end. So they are checked here, on
 * the one place that now does it.
 */
class WhatAWeightedSumRunsBetweenIsAskedInOnePlaceTest {

    private static Rational num(long whole) {
        return Rational.of(whole);
    }

    private static Map<String, Rational> weighing(Object... pairs) {
        Map<String, Rational> out = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            out.put((String) pairs[i], num((Integer) pairs[i + 1]));
        }
        return out;
    }

    private static Reach shut(long least, long most) {
        return Reach.between(RationalCut.inclusive(num(least)), RationalCut.inclusive(num(most)));
    }

    private static Reach reachOf(Map<String, Rational> coefs, Map<String, Reach> positions) {
        return Reach.of(coefs, Rational.ZERO, positions::get);
    }

    @Test
    void aSumRunsBetweenWhatItsPartsRunBetween() {
        assertEquals(shut(0, 30), reachOf(weighing("a", 3), Map.of("a", shut(0, 10))));
        assertEquals(shut(3, 17),
                reachOf(weighing("a", 1, "b", 2), Map.of("a", shut(1, 5), "b", shut(1, 6))));
    }

    /**
     * A position pulling the sum down contributes least at its greatest.
     *
     * <p>Read from the same end regardless, this is wrong wherever a rule subtracts — and it comes
     * out as a threshold declared outside a quantity's reach when it is inside, which is a border
     * not drawn rather than anything nearer the mistake.
     */
    @Test
    void whichEndOfAPositionIsReadIsTheSignOfItsWeight() {
        assertEquals(shut(-6, -1), reachOf(weighing("a", -1), Map.of("a", shut(1, 6))));
        assertEquals(shut(-5, 4),
                reachOf(weighing("a", 1, "b", -1), Map.of("a", shut(0, 5), "b", shut(1, 5))),
                "least is a at nought with b at five; most is a at five with b at one");
    }

    /** The sum reaches its end only where every part does. An end wrongly called reachable is a
     *  point a search is sent to look for and never finds. */
    @Test
    void oneUnreachedEndMakesTheWholeSumUnreached() {
        Map<String, Reach> positions = new LinkedHashMap<>();
        positions.put("a", shut(0, 5));
        positions.put("b", Reach.between(RationalCut.inclusive(num(0)),
                RationalCut.exclusive(num(4))));
        Reach runs = reachOf(weighing("a", 1, "b", 1), positions);
        assertEquals(RationalCut.inclusive(num(0)), runs.least(), "both reach their least");
        assertEquals(RationalCut.exclusive(num(9)), runs.most(), "b never quite reaches four");
    }

    /** And an unreached end on the far side of a negative weight is the one that goes unreached. */
    @Test
    void anUnreachedEndTravelsWithTheSignToo() {
        Map<String, Reach> positions = Map.of("a", Reach.between(
                RationalCut.exclusive(num(1)), RationalCut.inclusive(num(6))));
        Reach runs = reachOf(weighing("a", -1), positions);
        assertEquals(RationalCut.inclusive(num(-6)), runs.least());
        assertEquals(RationalCut.exclusive(num(-1)), runs.most(),
                "a never quite reaches one, so minus a never quite reaches minus one");
    }

    @Test
    void aPositionUnboundedTheWayItMattersLeavesTheSumUnbounded() {
        Map<String, Reach> positions = new LinkedHashMap<>();
        positions.put("a", shut(0, 5));
        positions.put("b", Reach.between(RationalCut.inclusive(num(0)), null));
        Reach runs = reachOf(weighing("a", 1, "b", 1), positions);
        assertEquals(RationalCut.inclusive(num(0)), runs.least());
        assertNull(runs.most(), "nothing bounds b above, so nothing bounds the sum above");
    }

    @Test
    void aPositionNothingIsKnownAboutRunsTheWholeWay() {
        assertTrue(reachOf(weighing("a", 1), Map.of()).saysNothing());
        assertTrue(Reach.ANYWHERE.saysNothing());
    }

    @Test
    void theConstantMovesBothEnds() {
        assertEquals(shut(10, 15),
                Reach.of(weighing("a", 1), num(10), atom -> shut(0, 5)));
    }
}
