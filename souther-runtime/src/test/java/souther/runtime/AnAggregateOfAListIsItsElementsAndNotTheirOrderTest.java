package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.BiFunction;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A sum or a product of a list is its elements' and not their order's: the value, whether it is
 * refused, and — held to an allowance — what it costs.
 *
 * <p>A run of two-term sums or products asks every partial answer to be held and pays for each
 * step as its order makes it. So a partial answer past the range refuses a list whose answer is
 * within it, and an allowance runs out on one order of a list that another order of the same list
 * fits in. Each aggregate is asked here of every order of one list, and answers the same.
 */
class AnAggregateOfAListIsItsElementsAndNotTheirOrderTest {

    /** A tenth to the power of a thousand: added to one, a thousand digits long. */
    private static final Rational FINE = Rational.of(new BigDecimal(BigInteger.ONE, 1000));

    @Test
    void aRationalSumHeldToAnAllowanceFitsItWhateverTheOrder() {
        Rational negative = Rational.ZERO.minus(FINE);
        // Enough for the fine terms to cancel and the one to be added, and not for a fine term
        // aligned with the one.
        WorkCheckpoint limited = pieces -> {
            if (pieces > 100) {
                throw new IllegalStateException("past the allowance: " + pieces);
            }
        };
        for (List<Rational> order : orders(List.of(FINE, negative, Rational.ONE))) {
            assertEquals(Rational.ONE, Lists.sumRational(order, limited),
                    () -> "in the order " + order);
        }
        sameEveryWay(List.of(FINE, negative, Rational.ONE, Rational.of(new BigDecimal("2.5"))),
                Lists::sumRational);
    }

    @Test
    void anIntSumIsRefusedOnlyWhereTheTotalIsPastTheRange() {
        for (List<Long> order : orders(List.of(Long.MAX_VALUE, 1L, -1L))) {
            assertEquals(Long.MAX_VALUE, Lists.sumInt(order, WorkCheckpoint.NONE),
                    () -> "in the order " + order);
        }
        for (List<Long> order : orders(List.of(Long.MAX_VALUE, 1L))) {
            assertThrows(ConstraintViolation.class, () -> Lists.sumInt(order, WorkCheckpoint.NONE));
        }
    }

    @Test
    void anIntProductWithANoughtIsNoughtWhateverTheOrder() {
        for (List<Long> order : orders(List.of(Long.MAX_VALUE, 2L, 0L))) {
            assertEquals(0L, Lists.productInt(order, WorkCheckpoint.NONE),
                    () -> "in the order " + order);
        }
        for (List<Long> order : orders(List.of(Long.MAX_VALUE, 2L))) {
            assertThrows(ConstraintViolation.class,
                    () -> Lists.productInt(order, WorkCheckpoint.NONE));
        }
    }

    @Test
    void aDecimalSumIsOneValueAndOneCostWhateverTheOrder() {
        BigDecimal fine = new BigDecimal(BigInteger.ONE, 1000);
        List<BigDecimal> terms = List.of(fine, BigDecimal.ONE, fine.negate(),
                new BigDecimal("2.50"));
        for (List<BigDecimal> order : orders(terms)) {
            BigDecimal paid = Lists.sumDecimal(order, pieces -> { });
            BigDecimal free = Lists.sumDecimal(order, WorkCheckpoint.NONE);
            assertEquals(free, paid, () -> "with and without an allowance, in the order " + order);
            assertEquals(1000, paid.scale(), "at the greatest scale of its terms");
            assertEquals(0, paid.compareTo(new BigDecimal("3.5")));
        }
        sameEveryWay(terms, Lists::sumDecimal);
    }

    @Test
    void aDecimalProductIsRefusedOnlyWhereItsScaleIs() {
        BigDecimal fine = new BigDecimal(BigInteger.ONE, 2_000_000_000);
        BigDecimal coarse = new BigDecimal(BigInteger.ONE, -2_000_000_000);
        for (List<BigDecimal> order : orders(List.of(fine, fine, coarse))) {
            assertEquals(fine, Lists.productDecimal(order, WorkCheckpoint.NONE),
                    () -> "in the order " + order);
        }
        sameEveryWay(List.of(fine, fine, coarse, new BigDecimal("1.5")), Lists::productDecimal);
    }

    @Test
    void aRationalProductIsRefusedOnlyWhereItsExponentsAre() {
        Rational up = new Rational(BigInteger.ONE, BigInteger.ONE, 1L << 62, 0);
        Rational down = new Rational(BigInteger.ONE, BigInteger.ONE, -(1L << 62), 0);
        for (List<Rational> order : orders(List.of(up, up, down))) {
            assertEquals(up, Lists.productRational(order, WorkCheckpoint.NONE),
                    () -> "in the order " + order);
        }
        sameEveryWay(List.of(up, up, down, Rational.of(new BigDecimal("1.5"))),
                Lists::productRational);
    }

    /**
     * And it costs no more than a run of {@code +} over a list that run is cheap for: many terms
     * of one scale, where the run's partial sum is never much longer than a term. What a term of a
     * scale is paid for is bounded by what the scale's terms can come to, which for these is the
     * longest of them and a carry — not every term's length together.
     */
    @Test
    void aSumOfManyOrdinaryTermsCostsWhatARunOfThemDoes() {
        List<BigDecimal> decimals = new ArrayList<>();
        List<Rational> rationals = new ArrayList<>();
        for (int i = 1; i <= 2000; i++) {
            decimals.add(new BigDecimal(BigInteger.valueOf(i * 7919L), 2));
            rationals.add(Rational.of(new BigDecimal(BigInteger.valueOf(i * 7919L), 2)));
        }
        long[] run = {0};
        BigDecimal byRun = BigDecimal.ZERO;
        Rational byRunExactly = Rational.ZERO;
        for (int i = 0; i < decimals.size(); i++) {
            byRun = DecimalMath.add(byRun, decimals.get(i), pieces -> run[0] += pieces);
            byRunExactly = byRunExactly.plus(rationals.get(i), pieces -> run[0] += pieces);
        }
        long[] one = {0};
        assertEquals(byRun, Lists.sumDecimal(decimals, pieces -> one[0] += pieces));
        assertEquals(byRunExactly, Lists.sumRational(rationals, pieces -> one[0] += pieces));
        long ran = run[0];
        long summed = one[0];
        assertTrue(summed <= 4 * ran + 4 * 2 * decimals.size(),
                () -> "one sum costs " + summed + " where a run of them costs " + ran);
    }

    /** {@code aggregate} of every order of {@code elements}, held to a counting allowance: one
     *  answer, and one cost. */
    private static <T, R> void sameEveryWay(List<T> elements,
                                            BiFunction<List<T>, WorkCheckpoint, R> aggregate) {
        R first = null;
        long firstCost = -1;
        for (List<T> order : orders(elements)) {
            long[] spent = {0};
            R answer = aggregate.apply(order, pieces -> spent[0] += pieces);
            if (firstCost < 0) {
                first = answer;
                firstCost = spent[0];
                continue;
            }
            R expected = first;
            long expectedCost = firstCost;
            assertEquals(expected, answer, () -> "the answer in the order " + order);
            assertEquals(expectedCost, spent[0], () -> "what it cost in the order " + order);
        }
    }

    /** Every order of {@code elements}. */
    private static <T> List<List<T>> orders(List<T> elements) {
        if (elements.isEmpty()) {
            return List.of(List.of());
        }
        List<List<T>> out = new ArrayList<>();
        for (int i = 0; i < elements.size(); i++) {
            List<T> rest = new ArrayList<>(elements);
            T first = rest.remove(i);
            for (List<T> tail : orders(rest)) {
                List<T> one = new ArrayList<>();
                one.add(first);
                one.addAll(tail);
                out.add(one);
            }
        }
        return out;
    }
}
