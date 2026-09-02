package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What is derived over positions whose values fill, checked against arithmetic that shares nothing
 * with it.
 *
 * <p>The whole-number checks enumerate: every position is bounded to a small range, so the points in
 * it are all the points there are, and "nothing is left" is decided rather than merely not
 * contradicted. Over decimals there is no enumerating — between any two values lie infinitely many —
 * so the check here is a second piece of arithmetic instead: Fourier–Motzkin elimination over exact
 * ratios, which decides linear arithmetic over the rationals and is written out below, sharing with
 * the implementation only {@link Rational}.
 *
 * <p><b>What it can and cannot say.</b> Souther's decimals are finite decimals and not the rationals:
 * {@code 3 * a} comes arbitrarily close to one and never arrives, so this compiler answers
 * {@code 3a <= 1} with {@code 3a < 1} — which is right, and is not something arithmetic over the
 * rationals can confirm, since over those a third is a perfectly good value. Elimination is therefore
 * no oracle for the strictness.
 *
 * <p>It is an oracle for the value, and that is where an unsound narrowing would show. The one thing
 * being a finite decimal ever does to a bound is refuse the value it already stopped at — the cut
 * never moves. So the value this compiler derives must be one the rationals allow, and a bound
 * derived tighter than the rationals allow is wrong however the decimals are counted.
 *
 * <pre>
 *     derived value is never below what elimination allows     (an upper bound)
 *     derived value is never above what elimination allows     (a lower bound)
 *     where the two values agree, ours may be the stricter     (and only off the image)
 * </pre>
 *
 * <p>Looser is expected and is not a failure: narrowing a box one rule at a time is weaker than
 * eliminating variables, so this compiler answers with less than elimination wherever a bound needs
 * two rules combined.
 */
class WhatIsDerivedOverDecimalsIsNeverTighterThanTheRationalsAllowTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");
    private static final int CASES = 400;

    private record Written(Map<String, Rational> coefs, Rational constant, Rel rel) {}

    private static Rational num(long whole) {
        return Rational.of(whole);
    }

    private static Rational ratio(long numerator, long denominator) {
        return Rational.of(java.math.BigInteger.valueOf(numerator),
                java.math.BigInteger.valueOf(denominator));
    }

    // --- the arithmetic this is checked against ------------------------------------------------------

    /** {@code Σ c·x <= k}, or {@code < k} when strict. */
    private record Row(Map<String, Rational> coefs, Rational at, boolean strict) {

        Rational weightOf(String position) {
            return coefs.getOrDefault(position, Rational.ZERO);
        }
    }

    /**
     * The rows with {@code position} eliminated: every pair of a row bounding it above and one
     * bounding it below is combined, and rows that do not name it are kept.
     *
     * <p>Fourier–Motzkin. Scaling each side so the weights cancel is exact here because the
     * arithmetic is ratios; done in decimals it would round, and a bound that rounds is not an oracle
     * for one that does not.
     */
    private static List<Row> eliminating(String position, List<Row> rows) {
        List<Row> above = new ArrayList<>();
        List<Row> below = new ArrayList<>();
        List<Row> without = new ArrayList<>();
        for (Row row : rows) {
            int sign = row.weightOf(position).signum();
            if (sign > 0) {
                above.add(row);
            } else if (sign < 0) {
                below.add(row);
            } else {
                without.add(row);
            }
        }
        for (Row upper : above) {
            for (Row lower : below) {
                Rational up = upper.weightOf(position);
                Rational down = lower.weightOf(position).negated();
                Map<String, Rational> coefs = new LinkedHashMap<>();
                for (String each : namedIn(List.of(upper, lower))) {
                    Rational combined = upper.weightOf(each).dividedBy(up)
                            .plus(lower.weightOf(each).dividedBy(down));
                    if (!combined.isZero()) {
                        coefs.put(each, combined);
                    }
                }
                without.add(new Row(coefs,
                        upper.at().dividedBy(up).plus(lower.at().dividedBy(down)),
                        upper.strict() || lower.strict()));
            }
        }
        return without;
    }

    private static Set<String> namedIn(List<Row> rows) {
        Set<String> out = new LinkedHashSet<>();
        rows.forEach(row -> out.addAll(row.coefs().keySet()));
        return out;
    }

    /** What the rows leave {@code position} over the rationals, either end null for no bound. */
    private static Reach eliminatingDownTo(String position, List<Row> rows) {
        List<Row> left = rows;
        for (String other : POSITIONS) {
            if (!other.equals(position)) {
                left = eliminating(other, left);
            }
        }
        RationalCut most = null;
        RationalCut least = null;
        for (Row row : left) {
            Rational weight = row.weightOf(position);
            if (weight.isZero()) {
                continue;   // a row with nothing left in it says whether the system holds, not where
            }
            RationalCut cut = new RationalCut(row.at().dividedBy(weight.abs()), !row.strict());
            if (weight.signum() > 0) {
                most = RationalCut.tighterUpper(most, cut);
            } else {
                least = RationalCut.tighterLower(least,
                        new RationalCut(cut.at().negated(), cut.inclusive()));
            }
        }
        return Reach.between(least, most);
    }

    /** Whether the rows hold at all over the rationals. */
    private static boolean anyRationalPointSatisfies(List<Row> rows) {
        List<Row> left = rows;
        for (String each : POSITIONS) {
            left = eliminating(each, left);
        }
        for (Row row : left) {
            if (!row.coefs().isEmpty()) {
                continue;
            }
            int sign = row.at().signum();
            if (row.strict() ? sign <= 0 : sign < 0) {
                return false;
            }
        }
        return true;
    }

    // --- and the check --------------------------------------------------------------------------------

    @Test
    void noBoundIsTighterThanTheRationalsAllow() {
        Random dice = new Random(1439);
        int narrowed = 0;
        for (int round = 0; round < CASES; round++) {
            List<Written> written = someRules(dice);
            List<Row> rows = asRows(written);
            if (!anyRationalPointSatisfies(rows)) {
                continue;   // nothing to be tight about
            }
            ClosedState<String> closed = ClosedState.of(read(written), atom -> Granularity.DENSE);
            if (closed.holdsNothing()) {
                continue;   // said over decimals and not over the rationals; see the class comment
            }
            for (String position : POSITIONS) {
                Reach allowed = eliminatingDownTo(position, rows);
                RationalCut most = closed.box().mostOf(position);
                RationalCut least = closed.box().leastOf(position);
                if (most != null) {
                    narrowed++;
                    assertFalse(allowed.most() == null,
                            () -> "bounded " + position + " above where the rationals leave it"
                                    + " unbounded: " + written);
                    assertTrue(most.at().compareTo(allowed.most().at()) >= 0,
                            () -> "derived " + position + " <= " + most.at() + " where the rationals"
                                    + " allow only " + allowed.most().at() + ": " + written);
                }
                if (least != null) {
                    assertFalse(allowed.least() == null,
                            () -> "bounded " + position + " below where the rationals leave it"
                                    + " unbounded: " + written);
                    assertTrue(least.at().compareTo(allowed.least().at()) <= 0,
                            () -> "derived " + position + " >= " + least.at() + " where the rationals"
                                    + " allow only " + allowed.least().at() + ": " + written);
                }
            }
        }
        assertTrue(narrowed > CASES / 4,
                "only " + narrowed + " bounds were derived at all, so this checked little");
    }

    /** And where the two agree on the value, ours is the stricter only where the value is one the
     *  sum cannot take. */
    @Test
    void whereTheValuesAgreeOursIsStricterOnlyOffTheImage() {
        Random dice = new Random(600);
        int checked = 0;
        for (int round = 0; round < CASES; round++) {
            List<Written> written = someRules(dice);
            List<Row> rows = asRows(written);
            if (!anyRationalPointSatisfies(rows)) {
                continue;
            }
            ClosedState<String> closed = ClosedState.of(read(written), atom -> Granularity.DENSE);
            if (closed.holdsNothing()) {
                continue;
            }
            for (String position : POSITIONS) {
                RationalCut most = closed.box().mostOf(position);
                RationalCut allowed = eliminatingDownTo(position, rows).most();
                if (most == null || allowed == null
                        || most.at().compareTo(allowed.at()) != 0
                        || most.inclusive() == allowed.inclusive()) {
                    continue;
                }
                checked++;
                assertFalse(most.inclusive(),
                        () -> "ours admits a value the rationals refuse at " + position);
                assertFalse(new AdditiveImage.OverFiniteDecimals(Rational.ONE)
                                .contains(most.at()),
                        () -> "ours refuses " + most.at() + " at " + position + ", which is a"
                                + " decimal the position can take: " + written);
            }
        }
        // No floor on `checked`: the two may simply never disagree, and a run in which they do not
        // is a run with nothing to check rather than a run that checked too little. Counted and
        // reported instead of asserted, since a counter is never below nought and an assertion that
        // it is not would say nothing at all.
        System.out.println("strictness differed at " + checked + " bounds of " + CASES + " systems");
    }

    /** The case the whole distinction is about, spelled out. */
    @Test
    void aThirdIsNotADecimalSoTheBoundStopsShortOfIt() {
        List<Written> written = List.of(new Written(Map.of("a", num(3)), num(-1), Rel.LE));
        ClosedState<String> closed = ClosedState.of(read(written), atom -> Granularity.DENSE);

        assertEquals(RationalCut.exclusive(ratio(1, 3)), closed.box().mostOf("a"),
                "3a <= 1 leaves a under a third and never at it");
        assertEquals(RationalCut.inclusive(ratio(1, 3)),
                eliminatingDownTo("a", asRows(written)).most(),
                "where over the rationals a third is a value like any other");
    }

    // --- the rules ------------------------------------------------------------------------------------

    private static List<Written> someRules(Random dice) {
        List<Written> out = new ArrayList<>();
        // A bound or two on the positions themselves, because narrowing a box needs somewhere to
        // start: a rule over three positions none of which is bounded says nothing about any of
        // them, and a run of those would be four hundred cases checking nothing.
        for (String position : POSITIONS) {
            if (dice.nextBoolean()) {
                out.add(new Written(Map.of(position, Rational.ONE),
                        num(dice.nextInt(9) - 8), Rel.GE));
            }
            if (dice.nextBoolean()) {
                out.add(new Written(Map.of(position, Rational.ONE),
                        num(-dice.nextInt(9)), Rel.LE));
            }
        }
        int howMany = 2 + dice.nextInt(3);
        for (int i = 0; i < howMany; i++) {
            Map<String, Rational> coefs = new LinkedHashMap<>();
            for (String position : POSITIONS) {
                int weight = dice.nextInt(7) - 3;
                if (weight != 0) {
                    coefs.put(position, num(weight));
                }
            }
            if (coefs.isEmpty()) {
                continue;
            }
            Rel rel = switch (dice.nextInt(4)) {
                case 0 -> Rel.LT;
                case 1 -> Rel.GE;
                case 2 -> Rel.GT;
                default -> Rel.LE;
            };
            out.add(new Written(coefs, num(dice.nextInt(17) - 8), rel));
        }
        return out;
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (Written each : written) {
            if (AffineConstraint.of(each.coefs(), each.constant(), each.rel(),
                    atom -> Granularity.DENSE) instanceof Read.Stated<String> stated) {
                out.add(stated.constraint());
            }
        }
        return out;
    }

    /** The rules as {@code Σ c·x <= k}, which is the one shape elimination works in. */
    private static List<Row> asRows(List<Written> written) {
        List<Row> out = new ArrayList<>();
        for (Written each : written) {
            boolean flip = each.rel() == Rel.GE || each.rel() == Rel.GT;
            boolean strict = each.rel() == Rel.LT || each.rel() == Rel.GT;
            Map<String, Rational> coefs = new LinkedHashMap<>();
            each.coefs().forEach((position, weight) ->
                    coefs.put(position, flip ? weight.negated() : weight));
            Rational at = flip ? each.constant() : each.constant().negated();
            out.add(new Row(coefs, at, strict));
        }
        return out;
    }
}
