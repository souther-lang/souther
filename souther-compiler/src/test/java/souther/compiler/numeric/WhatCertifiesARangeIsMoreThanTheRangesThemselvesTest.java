package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What certifies a range is the ranges together with the relations the closure holds between them.
 *
 * <p>Two systems, and in neither of them do the ranges on their own state the rule. A difference is
 * held exactly by the closed relations and comes back proven; a hole is held by nothing and does
 * not. So what a range is certified by is not what the product of the ranges states, and a reader
 * taking the one for the other is reading an answer about a stronger object than the one it has.
 *
 * <p>And the two are not the same about the range either. The difference leaves every position
 * exactly what the rules leave it; the hole leaves a value admitted that no point carries. Which is
 * why failing to state a rule cannot be what decides it.
 *
 * <p>Enumerated rather than argued. Every position is bounded as part of the system, so the whole
 * numbers inside those bounds are all the points there are, and what the rules leave a position is
 * read off them.
 */
class WhatCertifiesARangeIsMoreThanTheRangesThemselvesTest {

    private static final int LOW = 0;
    private static final int HIGH = 7;

    /**
     * A difference: {@code a - b <= 2}, with both positions running 0 to 7.
     *
     * <p>Each position runs the whole way — an {@code a} of 7 stands beside a {@code b} of 5, and a
     * {@code b} of 0 beside an {@code a} of 2 — so what each is left is exactly its range. The bounds
     * still do not state the rule, because the corner they hold has {@code a} at 7 beside {@code b}
     * at 0.
     */
    @Test
    void aDifferenceIsProvenByRelationsTheRangesThemselvesDoNotHold() {
        NumericDomain<String> domain = domainOf(aDifference());

        // Each position runs the whole way, so the two ranges together hold `a = 7` beside `b = 0`,
        // which is seven apart. Their product does not state the rule.
        assertEquals(Set.of(0, 1, 2, 3, 4, 5, 6, 7), admittedAt(domain, "a"));
        assertEquals(Set.of(0, 1, 2, 3, 4, 5, 6, 7), admittedAt(domain, "b"));

        // And the rule comes back proven all the same, off the closed relation between them.
        assertTrue(domain.provenByTheBoxAndItsDifferences(
                atom("a").minus(atom("b")).minus(num(2)), Rel.LE));

        // Which is sound, and the points say so: what each position is left is exactly its range.
        assertEquals(carriedAt("a", aDifference()), admittedAt(domain, "a"));
        assertEquals(carriedAt("b", aDifference()), admittedAt(domain, "b"));
        assertEquals(
                new ProjectionCertification.Certified(
                        new ProjectionCertificate.ByBoxAndClosedDifferences()),
                domain.projectionCertification());
    }

    /**
     * A hole: {@code a /= 3}, over the same two positions.
     *
     * <p>The same failure to state, and here the bounds really are wider: a range cannot leave one
     * value out of the middle of itself, so the 3 stays admitted and no point carries it.
     */
    @Test
    void aHoleIsHeldByNothingAndLeavesAValueNoPointCarries() {
        NumericDomain<String> domain = domainOf(aHole());

        assertFalse(domain.provenByTheBoxAndItsDifferences(atom("a").minus(num(3)), Rel.NE),
                "a range cannot say a value in the middle of it is out");

        assertNotEquals(carriedAt("a", aHole()), admittedAt(domain, "a"));
        assertEquals(Set.of(3),
                difference(admittedAt(domain, "a"), carriedAt("a", aHole())),
                "the 3 is the whole of what the bounds admit and no point carries");
        assertEquals(new ProjectionCertification.NotEveryRuleIsProven(),
                domain.projectionCertification());
    }

    // --- the systems ------------------------------------------------------------------------------

    /** {@code Σ coefs·position + constant  rel  0}, as a rule is written before it is read. */
    private record Written(Map<String, Long> coefs, long constant, Rel rel) {}

    private static Written aDifference() {
        Map<String, Long> coefs = new LinkedHashMap<>();
        coefs.put("a", 1L);
        coefs.put("b", -1L);
        return new Written(coefs, -2, Rel.LE);
    }

    private static Written aHole() {
        return new Written(Map.of("a", 1L), -3, Rel.NE);
    }

    /**
     * The rule, beside the bounds that make the points enumerated below all the points there are.
     *
     * <p>The bounds are part of the system and not a range the enumeration was run over. A bound the
     * rules do not hold would narrow what the points say while leaving what the domain says alone,
     * and the two would be compared over different systems.
     */
    private static List<Written> systemOf(Written rule) {
        List<Written> out = new java.util.ArrayList<>();
        for (String position : List.of("a", "b")) {
            out.add(new Written(Map.of(position, 1L), -LOW, Rel.GE));
            out.add(new Written(Map.of(position, 1L), -HIGH, Rel.LE));
        }
        out.add(rule);
        return out;
    }

    private static NumericDomain<String> domainOf(Written rule) {
        NumericDomain<String> domain = NumericDomain.top();
        Map<String, Granularity> whole = Map.of("a", Granularity.DISCRETE,
                "b", Granularity.DISCRETE);
        for (Written each : systemOf(rule)) {
            domain = domain.assume(formOf(each), each.rel(), whole);
        }
        return domain;
    }

    private static LinearForm<String> formOf(Written written) {
        LinearForm<String> form = LinearForm.constant(BigDecimal.valueOf(written.constant()));
        for (Map.Entry<String, Long> each : written.coefs().entrySet()) {
            form = form.plus(atom(each.getKey()).times(BigDecimal.valueOf(each.getValue())));
        }
        return form;
    }

    // --- what the points say, and what the bounds say ---------------------------------------------

    /** Every value some point of the system carries at {@code position}. */
    private static Set<Integer> carriedAt(String position, Written rule) {
        List<Written> system = systemOf(rule);
        Set<Integer> out = new LinkedHashSet<>();
        for (int a = LOW; a <= HIGH; a++) {
            for (int b = LOW; b <= HIGH; b++) {
                Map<String, Integer> point = Map.of("a", a, "b", b);
                if (system.stream().allMatch(each -> holdsAt(each, point))) {
                    out.add(point.get(position));
                }
            }
        }
        return out;
    }

    /** Every whole number the bounds handed over admit at {@code position}. */
    private static Set<Integer> admittedAt(NumericDomain<String> domain, String position) {
        NumericDomain.Bounds bounds = domain.boundsOf(position);
        Set<Integer> out = new LinkedHashSet<>();
        for (int at = LOW; at <= HIGH; at++) {
            if (bounds.admits(Count.of(at))) {
                out.add(at);
            }
        }
        return out;
    }

    private static Set<Integer> difference(Set<Integer> wider, Set<Integer> narrower) {
        Set<Integer> out = new LinkedHashSet<>(wider);
        out.removeAll(narrower);
        return out;
    }

    private static boolean holdsAt(Written rule, Map<String, Integer> point) {
        long total = rule.constant();
        for (Map.Entry<String, Long> each : rule.coefs().entrySet()) {
            total += each.getValue() * point.get(each.getKey());
        }
        return switch (rule.rel()) {
            case LE -> total <= 0;
            case LT -> total < 0;
            case GE -> total >= 0;
            case GT -> total > 0;
            case EQ -> total == 0;
            case NE -> total != 0;
        };
    }

    private static LinearForm<String> atom(String a) {
        return LinearForm.atom(a);
    }

    private static LinearForm<String> num(long n) {
        return LinearForm.constant(BigDecimal.valueOf(n));
    }
}
