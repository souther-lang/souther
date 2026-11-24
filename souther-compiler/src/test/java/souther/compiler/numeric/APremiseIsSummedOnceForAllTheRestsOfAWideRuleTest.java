package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a rule over many positions costs grows with how many positions it names and not with how
 * many of them squared.
 *
 * <p>The rests of one half-space are one sum with a term changed each, so a premise is summed over
 * the terms of the question and of itself once and each rest then reads it in a step. A reading
 * that summed the premise afresh for each rest would cost the width of the rule for each of its
 * positions. What is held is the work counted when every rest of one rule is asked beside a few
 * premises over the same positions, at a width and at twice that.
 */
class APremiseIsSummedOnceForAllTheRestsOfAWideRuleTest {

    /** Positions, one letter each, so that a rule can name as many as the widest case needs. */
    private static final String POSITIONS = "abcdefghijklmnop";

    /** Rules over the first {@code width} positions, none of them a multiple of another. */
    private static List<AffineConstraint<String>> rulesOver(int width) {
        List<RulesAsWritten.Written> written = new ArrayList<>();
        for (int rule = 1; rule <= 4; rule++) {
            StringBuilder text = new StringBuilder();
            for (int at = 0; at < width; at++) {
                text.append(at == 0 ? "" : " + ").append(rule + at).append(POSITIONS.charAt(at));
            }
            written.add(RulesAsWritten.rule(text + " <= " + rule));
        }
        return RulesAsWritten.statedOnly(written, RulesNamingNoPositionInCommonCloseApartTest::spacing);
    }

    private static long workAskingEveryRestOfTheFirstRule(int width) {
        List<AffineConstraint<String>> rules = rulesOver(width);
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();
        Box<String> ends = Box.unbounded();
        FormReach<String> reading = FormReach.over(rules, ends, DifferenceBounds.over(rules, order),
                order).working(List.of(), new RoundWork<>(rules, ends));
        AffineConstraint<String> asking = rules.getFirst();
        AffineConstraint.HalfSpace<String> half = asking.halfSpaces().getFirst();
        FormReach<String>.Rests rests = reading.rests(asking, half);
        long before = FormReach.premisesWorked();
        for (String atom : half.form().atomsIn(order)) {
            rests.leastOfTheRest(atom);
        }
        return FormReach.premisesWorked() - before;
    }

    @Test
    void twiceTheWidthCostsLessThanThreeTimesTheWork() {
        long narrow = workAskingEveryRestOfTheFirstRule(4);
        long wide = workAskingEveryRestOfTheFirstRule(8);
        assertTrue(narrow > 0, "nothing was counted, so this holds nothing");
        // Linear in the width is twice as much and the square of it is four times; a premise
        // summed again for each rest is the square.
        assertTrue(wide < 3 * narrow, "twice the width cost " + wide
                + " where the narrower cost " + narrow);
    }
}
