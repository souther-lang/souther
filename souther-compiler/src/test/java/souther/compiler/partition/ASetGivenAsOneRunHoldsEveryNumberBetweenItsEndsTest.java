package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Ends a set gives as one run hold exactly its numbers: nothing between them is left out, and
 * nothing outside them is in.
 *
 * <p>What a walk handed those ends is bounded by. Its figure counts the numbers it admits, so a
 * number between the ends the set turns down is a step nothing pays for — and carried onto
 * another number first, as a quotient's ends are carried onto the place, one such number is as
 * many steps as the divisor is wide.
 *
 * <p>Ends given are held to that; a set giving none is not held to having holes. That side claims
 * less, and nothing reads it as more.
 */
class ASetGivenAsOneRunHoldsEveryNumberBetweenItsEndsTest {

    /** As far either way as the numbers are checked, which is past every end below. */
    private static final int FAR = 20;

    private static final List<NumericSet> SETS = List.of(
            new NumericSet.At(Count.of(5)),
            new NumericSet.InARun(run(0, true, 10, true)),
            new NumericSet.InARun(run(0, false, 10, false)),
            new NumericSet.InARun(new Band(Band.endAt(null, null, Towards.ABOVE),
                    Band.endAt(null, Bound.at(at(3), true), Towards.BELOW))),
            new NumericSet.InARunExcept(run(0, true, 10, true), List.of(Count.of(0))),
            new NumericSet.InARunExcept(run(0, true, 10, true), List.of(Count.of(5))),
            new NumericSet.AwayFrom(List.of(Count.of(3))));

    @Test
    void theEndsHoldEveryNumberOfTheSetAndNoOther() {
        List<String> apart = new ArrayList<>();
        int given = 0;
        for (NumericSet set : SETS) {
            NumericDomain.Bounds ends = set.asOneRun();
            if (ends == null) {
                continue;
            }
            given++;
            for (int k = -FAR; k <= FAR; k++) {
                Count number = Count.of(k);
                boolean between = above(ends.min(), k) && below(ends.max(), k);
                if (between != set.holds(number, Carrier.WHOLE)) {
                    apart.add(set + " gives " + ends + ", and " + k + " is "
                            + (between ? "between them and not held" : "held and outside them"));
                }
            }
        }
        assertEquals(List.of(), apart);
        assertTrue(given >= 3, "the sets that are runs give their ends, so this checked some");
    }

    /**
     * A shape that takes values out takes at least one.
     *
     * <p>Taking none out is the run, or the whole order, under a shape whose answers are given for
     * a set with something taken out of it — a state the shape would answer for wrongly, and one
     * no rule leaves.
     */
    @Test
    void takingNothingOutIsNotASetOfThatShape() {
        assertThrows(IllegalArgumentException.class,
                () -> new NumericSet.AwayFrom(List.of()));
        assertThrows(IllegalArgumentException.class,
                () -> new NumericSet.InARunExcept(run(0, true, 10, true), List.of()));
    }

    /** Every shape a set comes in is among the ones checked. */
    @Test
    void everyShapeIsChecked() {
        Set<Class<?>> shapes = Arrays.stream(NumericSet.class.getPermittedSubclasses())
                .collect(Collectors.toSet());
        Set<Class<?>> checked = SETS.stream().map(Object::getClass).collect(Collectors.toSet());
        assertEquals(shapes, checked);
    }

    private static boolean above(Endpoint end, int k) {
        if (end == null) {
            return true;
        }
        int c = BigDecimal.valueOf(k).compareTo(((Count) end.at()).at());
        return c > 0 || (c == 0 && end.inclusive());
    }

    private static boolean below(Endpoint end, int k) {
        if (end == null) {
            return true;
        }
        int c = BigDecimal.valueOf(k).compareTo(((Count) end.at()).at());
        return c < 0 || (c == 0 && end.inclusive());
    }

    private static Band run(long low, boolean lowIn, long high, boolean highIn) {
        return new Band(Band.endAt(null, Bound.at(at(low), lowIn), Towards.ABOVE),
                Band.endAt(null, Bound.at(at(high), highIn), Towards.BELOW));
    }

    private static Level at(long value) {
        return new Level.OnACarrier(Carrier.WHOLE, Count.of(value));
    }
}
