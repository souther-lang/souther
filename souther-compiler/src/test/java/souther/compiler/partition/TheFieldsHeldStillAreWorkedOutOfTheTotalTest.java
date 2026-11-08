package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * The values the fields held still are held at are worked out of the total
 * ({@link FieldsHeldForATotal#heldFor}) for the count the container holds, held to the totals
 * themselves: each value is in its field's run, and with them the field solved for makes up the
 * rest within its run over that many elements; and where the field solved for has the widest
 * run, every total that many elements of the fields' runs come to is given values.
 */
class TheFieldsHeldStillAreWorkedOutOfTheTotalTest {

    /** The counts the totals are asked over. */
    private static final int MOST = 3;

    @Test
    void theValuesWorkedOutComeToTheTotalAndEveryReachedTotalHasThem() {
        int asked = 0;
        int given = 0;
        List<int[]> runs = List.of(new int[] {0, 2}, new int[] {-1, 1}, new int[] {1, 3},
                new int[] {2, 2});
        for (int[] free : runs) {
            for (int[] first : runs) {
                for (int[] second : runs) {
                    for (int weightOfFirst : new int[] {1, -1}) {
                        for (int constant = 0; constant <= 1; constant++) {
                            for (int many = 1; many <= MOST; many++) {
                                for (int total = -12; total <= 24; total++) {
                                    asked++;
                                    given += heldOver(free, first, weightOfFirst, second,
                                            constant, many, total) ? 1 : 0;
                                }
                            }
                        }
                    }
                }
            }
        }
        assertNotEquals(0, given);
        assertNotEquals(asked, given);
    }

    /**
     * Whether {@code q·w + r}, held, and {@code f}, solved for, are given values for
     * {@code many} elements to come to {@code total}: values in the fields' runs that so many
     * elements come to it with, and values wherever so many reach it and {@code f} is widest.
     */
    private static boolean heldOver(int[] free, int[] first, int weightOfFirst, int[] second,
                                    int constant, int many, int total) {
        Map<String, FieldsHeldForATotal.Field> held = new LinkedHashMap<>();
        held.put("q", field(weightOfFirst, first));
        held.put("r", field(1, second));
        Map<String, ExactRatio> values = FieldsHeldForATotal.heldFor(held, field(1, free),
                ratio(constant), ratio(total), many, true, any -> true);
        boolean widest = free[1] - free[0] >= first[1] - first[0]
                && free[1] - free[0] >= second[1] - second[0];
        if (values == null) {
            if (widest && reached(total, many, constant, weightOfFirst, first, second, free)) {
                fail("no values for " + total + " of " + many + " over q" + range(first) + "·"
                        + weightOfFirst + " r" + range(second) + " f" + range(free) + " + "
                        + constant);
            }
            return false;
        }
        long q = whole(values.get("q"));
        long r = whole(values.get("r"));
        assertTrue(q >= first[0] && q <= first[1], values::toString);
        assertTrue(r >= second[0] && r <= second[1], values::toString);
        long rest = total - many * (constant + weightOfFirst * q + r);
        assertTrue(rest >= (long) many * free[0] && rest <= (long) many * free[1],
                () -> total + " of " + many + " with " + values);
        return true;
    }

    /** Two fields of one to three, two elements, come to five, which one element also comes to:
     *  the field held is held for two elements, at one, and not at what one element takes. */
    @Test
    void theFieldsAreHeldForTheCountTheyAreAskedFor() {
        Map<String, FieldsHeldForATotal.Field> held = new LinkedHashMap<>();
        held.put("q", field(1, new int[] {1, 3}));
        Map<String, ExactRatio> values = FieldsHeldForATotal.heldFor(held,
                field(1, new int[] {1, 3}), ExactRatio.ZERO, ratio(5), 2, true, any -> true);
        assertNotNull(values);
        assertEquals(1, whole(values.get("q")));
    }

    /** Two fields of two to eight tenths come to every number from four tenths to one and six
     *  tenths: the field held is held at a decimal, and no whole number need lie in its run. */
    @Test
    void aFieldOfDecimalsIsHeldAtADecimalOfItsRun() {
        Map<String, FieldsHeldForATotal.Field> held = new LinkedHashMap<>();
        held.put("q", new FieldsHeldForATotal.Field(ExactRatio.ONE, decimal("0.2"),
                decimal("0.8")));
        FieldsHeldForATotal.Field free = new FieldsHeldForATotal.Field(ExactRatio.ONE,
                decimal("0.2"), decimal("0.8"));
        for (String total : List.of("0.4", "1.0", "1.6", "1.13")) {
            Map<String, ExactRatio> values = FieldsHeldForATotal.heldFor(held, free,
                    ExactRatio.ZERO, decimal(total), 1, false, any -> true);
            assertNotNull(values, total);
            ExactRatio q = values.get("q");
            ExactRatio rest = decimal(total).minus(q).orNull();
            assertTrue(q.compareTo(decimal("0.2")) >= 0 && q.compareTo(decimal("0.8")) <= 0,
                    total + " " + values);
            assertTrue(rest.compareTo(decimal("0.2")) >= 0 && rest.compareTo(decimal("0.8")) <= 0,
                    total + " " + values);
        }
    }

    /** However many fields are held, one set of values is worked out: twenty fields of nought to
     *  one, held for a total of fifteen. */
    @Test
    void manyFieldsHeldAreWorkedOutOnce() {
        Map<Integer, FieldsHeldForATotal.Field> held = new LinkedHashMap<>();
        for (int i = 0; i < 20; i++) {
            held.put(i, field(1, new int[] {0, 1}));
        }
        Map<Integer, ExactRatio> values = FieldsHeldForATotal.heldFor(held,
                field(1, new int[] {0, 1}), ExactRatio.ZERO, ratio(15), 1, true, any -> true);
        assertNotNull(values);
        long sum = values.values().stream()
                .mapToLong(TheFieldsHeldStillAreWorkedOutOfTheTotalTest::whole).sum();
        assertTrue(sum == 15 || sum == 14, values::toString);
        assertEquals(20, values.size());
    }

    /** Whether {@code total} is what {@code many} elements come to, each element
     *  {@code constant + w·q + r + f} with each field anywhere in its run apart from the rest. */
    private static boolean reached(int total, int many, int constant, int weight, int[] q, int[] r,
                                   int[] f) {
        int low = constant + Math.min(weight * q[0], weight * q[1]) + r[0] + f[0];
        int high = constant + Math.max(weight * q[0], weight * q[1]) + r[1] + f[1];
        return total >= many * low && total <= many * high;
    }

    private static FieldsHeldForATotal.Field field(int weight, int[] run) {
        return new FieldsHeldForATotal.Field(ratio(weight), ratio(run[0]), ratio(run[1]));
    }

    /** The whole number {@code value} is. */
    private static long whole(ExactRatio value) {
        assertTrue(value.isWhole(), value::toString);
        return value.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger at)
                ? at.longValueExact() : Long.MIN_VALUE;
    }

    private static ExactRatio ratio(long whole) {
        return ExactRatio.of(BigInteger.valueOf(whole));
    }

    private static ExactRatio decimal(String written) {
        return ExactRatio.of(new BigDecimal(written));
    }

    private static String range(int[] run) {
        return "[" + run[0] + ", " + run[1] + "]";
    }
}
