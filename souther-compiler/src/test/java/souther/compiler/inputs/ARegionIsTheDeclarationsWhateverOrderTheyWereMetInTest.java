package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.ObservedValue;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.BinaryOperator;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Readings of one rule put together are one region whatever order and grouping they are put
 * together in: the declarations, what each holder is left, what was shown to hold at once, and how
 * far out a bound goes.
 */
class ARegionIsTheDeclarationsWhateverOrderTheyWereMetInTest {

    private static final ABoundThatKeepsEveryRunGoing.Held OPEN =
            new ABoundThatKeepsEveryRunGoing.Held(null, null);

    private static ABoundThatKeepsEveryRunGoing on(String parameter, boolean atMost, long at) {
        return new ABoundThatKeepsEveryRunGoing(
                new ABoundThatKeepsEveryRunGoing.Holder.AParameter(parameter, "Int"), atMost,
                BigInteger.valueOf(at), new ObservedValue.Integer(at));
    }

    /** One reading's region: {@code bounds}, with what it says their one holder is left. */
    private static Optional<WhatKeepsEveryRunGoing> reading(
            ABoundThatKeepsEveryRunGoing.Held left, ABoundThatKeepsEveryRunGoing... bounds) {
        Map<ABoundThatKeepsEveryRunGoing.Holder, ABoundThatKeepsEveryRunGoing.Held> held =
                new LinkedHashMap<>();
        for (ABoundThatKeepsEveryRunGoing each : bounds) {
            held.put(each.holder(), left);
        }
        return WhatKeepsEveryRunGoing.of(List.of(bounds), held);
    }

    private static final BinaryOperator<Optional<WhatKeepsEveryRunGoing>> TOGETHER =
            WhatKeepsEveryRunGoing::together;

    /** Every order of {@code a}, {@code b} and {@code c}, each put together both ways round. */
    private static List<Optional<WhatKeepsEveryRunGoing>> everyWay(
            Optional<WhatKeepsEveryRunGoing> a, Optional<WhatKeepsEveryRunGoing> b,
            Optional<WhatKeepsEveryRunGoing> c) {
        List<List<Optional<WhatKeepsEveryRunGoing>>> orders = List.of(List.of(a, b, c),
                List.of(a, c, b), List.of(b, a, c), List.of(b, c, a), List.of(c, a, b),
                List.of(c, b, a));
        return orders.stream().flatMap(order -> Stream.of(
                TOGETHER.apply(TOGETHER.apply(order.get(0), order.get(1)), order.get(2)),
                TOGETHER.apply(order.get(0), TOGETHER.apply(order.get(1), order.get(2)))))
                .toList();
    }

    /** A value holding all of it at once is shown wherever one reading showed it of everything
     *  the region declares on, put in first or last — and nowhere none did. */
    @Test
    void readingsPutTogetherInAnyOrderComeToOneRegion() {
        ABoundThatKeepsEveryRunGoing x = on("x", true, 10);
        ABoundThatKeepsEveryRunGoing y = on("y", true, 20);

        for (Optional<WhatKeepsEveryRunGoing> region : everyWay(reading(OPEN, x),
                reading(OPEN, y), WhatKeepsEveryRunGoing.of(List.of(x, y),
                        Map.of(x.holder(), OPEN, y.holder(), OPEN)))) {
            assertEquals(Set.of(x, y), region.orElseThrow().bounds());
            assertTrue(region.orElseThrow().heldTogether());
        }
        assertFalse(TOGETHER.apply(reading(OPEN, x), reading(OPEN, y)).orElseThrow()
                .heldTogether());
    }

    /**
     * What each reading says a holder is left is kept whichever bound of it is the tightest: the
     * three together hold {@code x} to 5..9 beside 8..10 and 0..6, which leaves it no value, so
     * there is no region however they are put together — though two of them leave one.
     */
    @Test
    void whatEachReadingSaysAHolderIsLeftIsKeptWhicheverBoundIsTightest() {
        Optional<WhatKeepsEveryRunGoing> a = reading(held(8, 10), on("x", true, 10));
        Optional<WhatKeepsEveryRunGoing> b = reading(held(0, 6), on("x", false, 5));
        Optional<WhatKeepsEveryRunGoing> c = reading(held(0, 9), on("x", true, 9));

        assertTrue(TOGETHER.apply(b, c).isPresent());
        assertEquals(List.of(), everyWay(a, b, c).stream().filter(Optional::isPresent).toList());
    }

    private static ABoundThatKeepsEveryRunGoing.Held held(long least, long greatest) {
        return new ABoundThatKeepsEveryRunGoing.Held(BigInteger.valueOf(least),
                BigInteger.valueOf(greatest));
    }

    @Test
    void howFarOutABoundGoesStandsOfTheSameDeclarationsMetInAnotherOrder() {
        ABoundThatKeepsEveryRunGoing x = on("x", true, 10);
        ABoundThatKeepsEveryRunGoing y = on("y", false, 0);
        Map<ABoundThatKeepsEveryRunGoing.Holder, ABoundThatKeepsEveryRunGoing.Held> open =
                Map.of(x.holder(), OPEN, y.holder(), OPEN);
        WhatKeepsEveryRunGoing one = WhatKeepsEveryRunGoing.of(List.of(x, y), open).orElseThrow();
        WhatKeepsEveryRunGoing other = WhatKeepsEveryRunGoing.of(List.of(y, x), open).orElseThrow()
                .asFarOutAsCanBe(Set.of(x));

        assertEquals(Set.of(x), TOGETHER.apply(Optional.of(one), Optional.of(other))
                .orElseThrow().asFarOutAsCanBe());
    }
}
