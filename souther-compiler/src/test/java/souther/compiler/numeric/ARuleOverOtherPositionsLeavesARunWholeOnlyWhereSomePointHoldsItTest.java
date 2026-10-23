package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule over positions no rule relates to a position bounds nothing of it but whether any value is
 * left at all, so the position is shown the whole of its run where that rule is shown to leave some
 * point — and not where nothing shows one.
 *
 * <p>Enumerated rather than argued. Every position runs nought to seven, so the whole numbers there
 * are all the points there are, and what {@code c} is left is read off them. The rules over
 * {@code a} and {@code b} are written at random, most of them neither a bound nor a difference, so
 * nothing proves them and the run of {@code c} is shown only through a point of the box they hold.
 */
class ARuleOverOtherPositionsLeavesARunWholeOnlyWhereSomePointHoldsItTest {

    private static final int LOW = 0;
    private static final int HIGH = 7;
    private static final int STATES = 2000;

    /** {@code Σ coefs·position + constant  rel  0}, as a rule is written before it is read. */
    private record Written(Map<String, Long> coefs, long constant, Rel rel) {}

    @Test
    void theRunShownIsOneEveryValueOfWhichSomePointCarries() {
        Random random = new Random(2678);
        int shownBesideAnUnprovenRule = 0;
        int leftNothing = 0;
        for (int s = 0; s < STATES; s++) {
            List<Written> rules = new ArrayList<>();
            for (int r = 1 + random.nextInt(2); r > 0; r--) {
                rules.add(ruleOverAAndB(random));
            }
            NumericDomain<String> domain = domainOf(rules);
            NumericDomain.Bounds run = domain.wholeRunOf("c");
            boolean somePoint = somePointHolds(rules);
            if (!somePoint) {
                leftNothing++;
                assertNull(run, () -> "no point holds " + rules + ", and c was shown " + run);
                continue;
            }
            if (run != null) {
                assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.of(LOW)),
                        Endpoint.inclusive(Count.of(HIGH))), run, rules::toString);
                if (!(domain.projectionCertification()
                        instanceof ProjectionCertification.Certified)) {
                    shownBesideAnUnprovenRule++;
                }
            }
        }
        assertTrue(shownBesideAnUnprovenRule > 0,
                "no state showed c's run beside a rule nothing proves, so a point was never asked");
        assertTrue(leftNothing > 0,
                "no state left no point, so whether one is asked for was never asked");
    }

    /**
     * {@code 4h - 3s < 0}, as a rule over two decimals, bounds nothing of a whole number apart from
     * both: {@code h} at nought and {@code s} at seven hold it.
     */
    @Test
    void aRuleOverTwoDecimalsNothingProvesLeavesAWholeNumberApartItsRun() {
        Map<String, Long> coefs = new LinkedHashMap<>();
        coefs.put("a", 4L);
        coefs.put("b", -3L);
        Map<String, Granularity> spacing = Map.of("a", Granularity.DENSE,
                "b", Granularity.DENSE, "c", Granularity.DISCRETE);
        NumericDomain<String> domain = domainOf(List.of(new Written(coefs, 0, Rel.LT)), spacing);

        assertEquals(new ProjectionCertification.NotEveryRuleIsProven(),
                domain.projectionCertification());
        assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.of(LOW)),
                Endpoint.inclusive(Count.of(HIGH))), domain.wholeRunOf("c"));
        assertNull(domain.wholeRunOf("a"), "a rule nothing proves leaves its own positions no run");
    }

    /**
     * A rule over two whole numbers nothing bounds, {@code a + 100b <= -1}, as a month and a day
     * of a date stand beside another date's before it: at nought both fail it, and {@code a} runs
     * down without end, so it is moved to where the rule holds and the point holds it.
     */
    @Test
    void aRuleOverPositionsWithNoEndIsHeldAtAPointMovedPastItsBound() {
        Map<String, Long> coefs = new LinkedHashMap<>();
        coefs.put("a", 1L);
        coefs.put("b", 100L);
        Map<String, Granularity> whole = Map.of("a", Granularity.DISCRETE,
                "b", Granularity.DISCRETE, "c", Granularity.DISCRETE);
        NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
        for (Written each : List.of(new Written(Map.of("c", 1L), -LOW, Rel.GE),
                new Written(Map.of("c", 1L), -HIGH, Rel.LE), new Written(coefs, 1, Rel.LE))) {
            domain = domain.assume(formOf(each), each.rel(), whole);
        }

        assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.of(LOW)),
                Endpoint.inclusive(Count.of(HIGH))), domain.wholeRunOf("c"));
    }

    /**
     * Three rules over three whole numbers from nought to four that no point holds, though the
     * ranges each leaves hold a value and nothing the reading of ranges does finds them empty.
     * The rules over the three leave {@code c} no run, since no row is left at all.
     */
    @Test
    void rulesOverOtherPositionsNoPointHoldsLeaveNoRun() {
        List<Written> rules = List.of(over(-2, -2, 2, 1, Rel.LE), over(-3, -2, 3, -2, Rel.GE),
                over(1, -3, -1, -8, Rel.LE));
        Map<String, Granularity> whole = Map.of("a", Granularity.DISCRETE,
                "b", Granularity.DISCRETE, "d", Granularity.DISCRETE, "c", Granularity.DISCRETE);
        NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
        List<Written> system = new ArrayList<>();
        for (String position : List.of("a", "b", "d")) {
            system.add(new Written(Map.of(position, 1L), 0, Rel.GE));
            system.add(new Written(Map.of(position, 1L), -4, Rel.LE));
        }
        system.add(new Written(Map.of("c", 1L), -LOW, Rel.GE));
        system.add(new Written(Map.of("c", 1L), -HIGH, Rel.LE));
        system.addAll(rules);
        for (Written each : system) {
            domain = domain.assume(formOf(each), each.rel(), whole);
        }
        for (int a = 0; a <= 4; a++) {
            for (int b = 0; b <= 4; b++) {
                for (int d = 0; d <= 4; d++) {
                    Map<String, Integer> point = Map.of("a", a, "b", b, "d", d);
                    assertTrue(!rules.stream().allMatch(each -> holdsAt(each, point)),
                            point::toString);
                }
            }
        }

        assertNull(domain.wholeRunOf("c"));
    }

    /** {@code a·a + b·b + d·d + constant  rel  0}. */
    private static Written over(long a, long b, long d, long constant, Rel rel) {
        Map<String, Long> coefs = new LinkedHashMap<>();
        coefs.put("a", a);
        coefs.put("b", b);
        coefs.put("d", d);
        return new Written(coefs, constant, rel);
    }

    private static Written ruleOverAAndB(Random random) {
        Map<String, Long> coefs = new LinkedHashMap<>();
        long a = random.nextInt(7) - 3L;
        long b = random.nextInt(7) - 3L;
        if (a != 0) {
            coefs.put("a", a);
        }
        if (b != 0 || coefs.isEmpty()) {
            coefs.put("b", b == 0 ? 1 : b);
        }
        Rel rel = List.of(Rel.LE, Rel.LT, Rel.GE, Rel.EQ, Rel.NE).get(random.nextInt(5));
        return new Written(coefs, random.nextInt(31) - 15L, rel);
    }

    /** Whether some whole point of the box holds every one of {@code rules}. */
    private static boolean somePointHolds(List<Written> rules) {
        for (int a = LOW; a <= HIGH; a++) {
            for (int b = LOW; b <= HIGH; b++) {
                Map<String, Integer> point = Map.of("a", a, "b", b);
                if (rules.stream().allMatch(each -> holdsAt(each, point))) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean holdsAt(Written rule, Map<String, Integer> point) {
        long sum = rule.constant();
        for (Map.Entry<String, Long> each : rule.coefs().entrySet()) {
            sum += each.getValue() * point.get(each.getKey());
        }
        return switch (rule.rel()) {
            case LT -> sum < 0;
            case LE -> sum <= 0;
            case GT -> sum > 0;
            case GE -> sum >= 0;
            case EQ -> sum == 0;
            case NE -> sum != 0;
        };
    }

    private static NumericDomain<String> domainOf(List<Written> rules) {
        return domainOf(rules, Map.of("a", Granularity.DISCRETE, "b", Granularity.DISCRETE,
                "c", Granularity.DISCRETE));
    }

    /** The rules, beside the bounds that make the points enumerated all the points there are. */
    private static NumericDomain<String> domainOf(List<Written> rules,
                                                  Map<String, Granularity> spacing) {
        List<Written> system = new ArrayList<>();
        for (String position : List.of("a", "b", "c")) {
            system.add(new Written(Map.of(position, 1L), -LOW, Rel.GE));
            system.add(new Written(Map.of(position, 1L), -HIGH, Rel.LE));
        }
        system.addAll(rules);
        NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
        for (Written each : system) {
            domain = domain.assume(formOf(each), each.rel(), spacing);
        }
        return domain;
    }

    private static LinearForm<String> formOf(Written written) {
        LinearForm<String> form = LinearForm.constant(ExactRatio.of(written.constant()));
        for (Map.Entry<String, Long> each : written.coefs().entrySet()) {
            form = SmallForm.small(form)
                    .plus(LinearForm.weighing(each.getKey(), ExactRatio.of(each.getValue()))).form();
        }
        return form;
    }
}
