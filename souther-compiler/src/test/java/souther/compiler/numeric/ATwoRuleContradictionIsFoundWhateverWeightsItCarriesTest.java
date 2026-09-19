package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two rules that add up to a statement no assignment satisfies leave nothing, whatever weights the
 * positions carry.
 *
 * <pre>
 *     guard y &lt;= 2 * x      guard y &gt;= 2 * x + 1
 * </pre>
 *
 * <p>is one and the same statement as the pair written with unit weights — at most nought and at
 * least one — and both are the rules leaving nothing. What decides it is the arithmetic and not how
 * heavily a position happens to be weighed, and not how wide a range the positions were taken in
 * over either.
 *
 * <p>Every one of these is a proof owed. Nothing here asks for the answer where the rules leave
 * something, nor for one where they leave nothing and this has not shown it: the contract is that
 * where this says the rules leave nothing, nothing is, and a case it does not settle today is one
 * it may settle tomorrow without anything having gone wrong.
 */
class ATwoRuleContradictionIsFoundWhateverWeightsItCarriesTest {

    private static final Map<String, Granularity> WHOLE = whole("x", "y", "z");

    private static Map<String, Granularity> whole(String... positions) {
        Map<String, Granularity> out = new LinkedHashMap<>();
        for (String each : positions) {
            out.put(each, Granularity.DISCRETE);
        }
        return out;
    }

    /** {@code constant + Σ weight·position}, written as pairs of a position and its weight. */
    private static LinearForm<String> form(long constant, Object... weighed) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        for (int each = 0; each < weighed.length; each += 2) {
            coefs.put((String) weighed[each], ExactRatio.of((Integer) weighed[each + 1]));
        }
        return new LinearForm<>(ExactRatio.of(constant), coefs);
    }

    /** {@code y <= weight·x} beside {@code y >= weight·x + 1}. */
    private static NumericDomain<String> theCrossedPair(int weight) {
        return NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .assume(form(0, "y", 1, "x", -weight), Rel.LE, WHOLE)
                .assume(form(-1, "y", 1, "x", -weight), Rel.GE, WHOLE);
    }

    private static NumericDomain<String> takenInOver(NumericDomain<String> domain, long upTo,
                                                     String... positions) {
        NumericDomain<String> out = domain;
        for (String each : positions) {
            out = out.assume(form(0, each, 1), Rel.GE, WHOLE)
                    .assume(form(-upTo, each, 1), Rel.LE, WHOLE);
        }
        return out;
    }

    @Test
    void theRulesLeaveNothingHoweverTheyWeighThePositions() {
        for (int weight : List.of(1, 2, 3, 7)) {
            assertTrue(theCrossedPair(weight).isBottom(),
                    "y <= " + weight + "x beside y >= " + weight + "x + 1 leaves nothing");
        }
    }

    @Test
    void andWhereBothPositionsAreWeighedRatherThanOne() {
        // 3x + 2y <= 1 beside 3x + 2y >= 2. Neither rule is a bound on a position or a difference
        // of two, and the pair is a contradiction that needs no third rule.
        assertTrue(NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .assume(form(-1, "x", 3, "y", 2), Rel.LE, WHOLE)
                .assume(form(-2, "x", 3, "y", 2), Rel.GE, WHOLE)
                .isBottom(), "a form bounded above below where it is bounded below");
    }

    @Test
    void andWhereTheTwoRulesAreWrittenAtDifferentScales() {
        // y - 2x >= 1 beside 6x - 3y >= 0, which is the second of the pair above written three times
        // over. What decides it is the form the two come to and not the numbers written.
        assertTrue(NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .assume(form(-1, "y", 1, "x", -2), Rel.GE, WHOLE)
                .assume(form(0, "x", 6, "y", -3), Rel.GE, WHOLE)
                .isBottom(), "one rule scaled is the same rule");
    }

    @Test
    void andHoweverWideTheRangeThePositionsWereTakenInOver() {
        // The narrow one is reached without any of this — the rules are read against the ends round
        // after round, and over a short run the ends cross before the rounds are spent. It is the
        // wide ones that say the answer does not turn on how far the rounds get.
        for (long upTo : List.of(10L, 1_000L, 1_000_000_000L)) {
            assertTrue(takenInOver(theCrossedPair(2), upTo, "x", "y").isBottom(),
                    "the same pair over positions taken in up to " + upTo);
        }
    }

    @Test
    void aFormIsEmptyAtOneValueOnlyWhereThatValueIsNotReachedFromBothSides() {
        ExactRatio five = ExactRatio.of(5);
        assertFalse(new Reach(ExactCut.inclusive(five), ExactCut.inclusive(five)).isEmpty(),
                "at least five and at most five runs at five");
        assertTrue(new Reach(ExactCut.exclusive(five), ExactCut.inclusive(five)).isEmpty(),
                "above five and at most five runs nowhere");
        assertTrue(new Reach(ExactCut.inclusive(ExactRatio.of(6)),
                ExactCut.inclusive(five)).isEmpty(), "at least six and at most five");
        assertFalse(new Reach(null, ExactCut.inclusive(five)).isEmpty(),
                "an end nobody found leaves it running that way");
    }

    @Test
    void andACycleOfDifferencesIsClosedOverItselfHowever() {
        NumericDomain<String> three = NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .assume(form(0, "y", 1, "x", -1), Rel.LE, WHOLE)
                .assume(form(0, "x", 1, "z", -1), Rel.LE, WHOLE)
                .assume(form(1, "z", 1, "y", -1), Rel.LE, WHOLE);
        assertTrue(three.isBottom(), "a cycle of differences summing below nought");
    }
}
