package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.RulesAsWritten.Written;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.rule;
import static souther.compiler.numeric.RulesAsWritten.statedOnly;

/**
 * A basis answers exactly only if every assumption its answer rests on holds, and each one is
 * checked in the one place it can be ({@link PrefixBasis}). This holds one rule or question to
 * each, as a pair: the rules that break exactly that assumption have no basis, and the same rules
 * with only that put right do.
 *
 * <p>A table and not a list of cases, so that an assumption added to the basis is a row added here
 * before it is trusted. Rules are built as they stand where the assumption is about how they were
 * written — a bound between two whole numbers, one the positions do not reach — since the rules a
 * caller reads are normalised when they are read and a rule handed in directly is not.
 */
class APrefixBasisIsChosenOnlyWhereEveryAssumptionOfItsAnswerHoldsTest {

    private static final CanonicalOrder<String> SPELLED = CanonicalOrder.asTheyAreSpelled();

    /** A bound no sum with a small number has a representation for. */
    private static final ExactRatio HUGE =
            ExactRatio.of(new BigDecimal(BigInteger.ONE, -Integer.MAX_VALUE));

    private static Granularity whole(String ignored) {
        return Granularity.DISCRETE;
    }

    private static Granularity filling(String ignored) {
        return Granularity.DENSE;
    }

    private static List<AffineConstraint<String>> stated(String... texts) {
        List<Written> written = new ArrayList<>();
        for (String text : texts) {
            written.add(rule(text));
        }
        return statedOnly(written,
                APrefixBasisIsChosenOnlyWhereEveryAssumptionOfItsAnswerHoldsTest::whole);
    }

    /** {@code coefs <= at}, or {@code < at}, as it stands: not read, so not made whole. */
    private static AffineConstraint<String> as(Map<String, ExactRatio> coefs, ExactRatio at,
                                               boolean inclusive) {
        return new AffineConstraint.HalfSpace<>(new CanonicalForm<>(coefs),
                new ExactCut(at, inclusive));
    }

    private static Map<String, ExactRatio> weighing(ExactRatio a, ExactRatio b) {
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        out.put("a", a);
        out.put("b", b);
        return out;
    }

    private static List<AffineConstraint<String>> beside(List<AffineConstraint<String>> rules,
                                                         AffineConstraint<String> more) {
        List<AffineConstraint<String>> out = new ArrayList<>(rules);
        out.add(more);
        return out;
    }

    /** What is assumed, the rules that break it, the same with it put right, and how positions are
     *  spaced in each. */
    private record Row(String assumption, List<AffineConstraint<String>> breaking,
                       List<AffineConstraint<String>> kept,
                       Function<String, Granularity> breakingSpacing,
                       Function<String, Granularity> keptSpacing) {

        Row(String assumption, List<AffineConstraint<String>> breaking,
            List<AffineConstraint<String>> kept) {
            this(assumption, breaking, kept,
                    APrefixBasisIsChosenOnlyWhereEveryAssumptionOfItsAnswerHoldsTest::whole,
                    APrefixBasisIsChosenOnlyWhereEveryAssumptionOfItsAnswerHoldsTest::whole);
        }
    }

    private static List<Row> table() {
        List<AffineConstraint<String>> ranges = stated("a >= 0", "a <= 5", "b >= 0", "b <= 5");
        ExactRatio half = ExactRatio.of(new BigDecimal("0.5"));
        ExactRatio quarter = ExactRatio.of(new BigDecimal("0.25"));
        ExactRatio one = ExactRatio.ONE;
        List<Row> out = new ArrayList<>();
        out.add(new Row("every rule is a half-space: not an equality",
                beside(ranges, new AffineConstraint.Equality<>(
                        new CanonicalForm<>(weighing(one, one)), ExactRatio.of(7))),
                beside(ranges, as(weighing(one, one), ExactRatio.of(7), true))));
        out.add(new Row("every rule is a half-space: not a hole",
                stated("a + b <= 7", "a /= 1"), stated("a + b <= 7", "a <= 1")));
        out.add(new Row("every position is a whole number",
                stated("a + b <= 3", "a + b + c <= 4"), stated("a + b <= 3", "a + b + c <= 4"),
                APrefixBasisIsChosenOnlyWhereEveryAssumptionOfItsAnswerHoldsTest::filling,
                APrefixBasisIsChosenOnlyWhereEveryAssumptionOfItsAnswerHoldsTest::whole));
        out.add(new Row("the supports are nested",
                stated("a + b <= 3", "b + c <= 3", "a >= 0", "b >= 0", "c >= 0"),
                stated("a + b <= 3", "a + b + c <= 3", "a >= 0", "b >= 0", "c >= 0")));
        out.add(new Row("every position is in a prefix",
                stated("a + b <= 3", "c <= 3"), stated("a + b <= 3", "a + b + c <= 3")));
        out.add(new Row("every rule is a coordinate or a difference once changed: not weighted",
                stated("2a + b <= 3", "a + b + c <= 4"), stated("a + b <= 3", "a + b + c <= 4")));
        out.add(new Row("every bound is a whole number: not one between two",
                beside(ranges, as(weighing(one, one), half, true)),
                beside(ranges, as(weighing(one, one), ExactRatio.ZERO, true))));
        out.add(new Row("every bound is a whole number: not one a weight scales off them",
                beside(ranges, as(weighing(half, half), quarter, true)),
                beside(ranges, as(weighing(half, half), half, true))));
        out.add(new Row("every bound is a bound the positions reach: not a strict one",
                beside(ranges, as(weighing(one, one), ExactRatio.of(7), false)),
                beside(ranges, as(weighing(one, one), ExactRatio.of(7), true))));
        List<Written> unsummed = List.of(rule("a <= 1"),
                new Written(weighing(one, one), HUGE.negated(), Rel.LE), rule("b >= -3"));
        out.add(new Row("every hop of the closure could be summed",
                statedOnly(unsummed,
                        APrefixBasisIsChosenOnlyWhereEveryAssumptionOfItsAnswerHoldsTest::whole),
                stated("a <= 1", "a + b <= 10", "b >= -3")));
        return out;
    }

    @Test
    void eachAssumptionIsCheckedWhereTheRulesThatBreakItHaveNoBasis() {
        List<Row> rows = table();
        assertTrue(rows.size() >= 10, "the table has " + rows.size() + " rows");
        for (Row row : rows) {
            assertNull(PrefixBasis.over(row.breaking(), row.breakingSpacing(), SPELLED),
                    "chosen though " + row.assumption() + " fails: " + row.breaking());
            assertNotNull(PrefixBasis.over(row.kept(), row.keptSpacing(), SPELLED),
                    "not chosen though only " + row.assumption() + " was put right: " + row.kept());
        }
    }

    /**
     * The one assumption that cannot be checked before a question is asked: what a question comes to
     * is summed when it is asked. Here {@code b + c} is the difference of two coordinates whose
     * bounds are far apart in scale, every bound of every single position is one the basis can
     * write, and nothing else relates the two. That it is bounded by nothing would be an answer, and
     * a wrong one, so it is not answered and the rules as they are stated are asked.
     */
    @Test
    void aQuestionWhoseSumTheArithmeticCannotHoldIsNotAnsweredAsBoundedByNothing() {
        List<Written> written = List.of(rule("a >= 3"), rule("a <= 5"), rule("a + b >= 0"),
                rule("a + b <= 10"), rule("a + b + c >= 0"),
                new Written(Map.of("a", ExactRatio.ONE, "b", ExactRatio.ONE, "c", ExactRatio.ONE),
                        HUGE.negated(), Rel.LE));
        List<AffineConstraint<String>> rules = statedOnly(written,
                APrefixBasisIsChosenOnlyWhereEveryAssumptionOfItsAnswerHoldsTest::whole);
        ClosedState<String> state = ClosedState.closedTogether(rules,
                APrefixBasisIsChosenOnlyWhereEveryAssumptionOfItsAnswerHoldsTest::whole, SPELLED);
        Map<String, ExactRatio> bPlusC = Map.of("b", ExactRatio.ONE, "c", ExactRatio.ONE);
        Map<String, ExactRatio> b = Map.of("b", ExactRatio.ONE);

        assertNotNull(PrefixBasis.over(rules,
                APrefixBasisIsChosenOnlyWhereEveryAssumptionOfItsAnswerHoldsTest::whole, SPELLED));
        assertInstanceOf(PrefixBasis.Highest.Within.class, state.highestInBasis(b, ExactRatio.ZERO));
        assertSame(PrefixBasis.Highest.NOT_ANSWERED, state.highestInBasis(bPlusC, ExactRatio.ZERO));
    }
}
