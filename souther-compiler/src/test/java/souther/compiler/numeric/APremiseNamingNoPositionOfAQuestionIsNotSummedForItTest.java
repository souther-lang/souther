package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A premise that names no position of a question has no sum taken of it for the question.
 *
 * <p>What such a premise leaves is the question beside it, and whether it is passed over is read
 * from the ends as they are. Summing it for the question is a cost for every premise of the round
 * on every question asked, and a round of many rules over positions of their own is mostly premises
 * of that kind — a cost that was not there before the sums of a premise were kept.
 *
 * <p>One question and one premise that names a position of it; the rules beside them are the same
 * rules however many there are, so the count taken is what says whether they are summed for.
 */
class APremiseNamingNoPositionOfAQuestionIsNotSummedForItTest {

    /** Positions of their own, two to a rule. */
    private static final List<String> OTHERS = List.of("p", "q", "r", "s", "t", "w", "x", "y");

    /** {@code a + b + cc <= 0}, and {@code b + d <= 3} naming a position of the rest of {@code a}. */
    private static List<AffineConstraint<String>> rulesBeside(int others) {
        List<String> written = new ArrayList<>(List.of("a + b + cc <= 0", "b + d <= 3"));
        for (int i = 0; i < others; i++) {
            written.add(OTHERS.get(2 * i) + " + " + OTHERS.get(2 * i + 1) + " <= 1");
        }
        return RulesAsWritten.statedOnly(written.stream().map(RulesAsWritten::rule).toList(),
                RulesNamingNoPositionInCommonCloseApartTest::spacing);
    }

    private static long sumsTakenAskingEveryRest(int others) {
        List<AffineConstraint<String>> rules = rulesBeside(others);
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();
        Box<String> ends = Box.unbounded();
        FormReach<String> reading = FormReach.over(rules, ends, DifferenceBounds.over(rules, order),
                order).working(List.of(), new RoundWork<>(rules, ends));
        AffineConstraint<String> asking = rules.getFirst();
        AffineConstraint.HalfSpace<String> half = asking.halfSpaces().getFirst();
        FormReach<String>.Rests rests = reading.rests(asking, half);
        for (String atom : half.form().atomsIn(order)) {
            rests.leastOfTheRest(atom);
        }
        return reading.sumsTaken();
    }

    @Test
    void rulesNamingNoPositionOfTheQuestionAreNotSummedFor() {
        assertEquals(sumsTakenAskingEveryRest(0), sumsTakenAskingEveryRest(4),
                "a sum was taken for a premise that names none of the question's positions");
    }

    /** The rests of {@code a} and of {@code cc} hold {@code b}, which the premise names; the rest of
     *  {@code b} holds neither {@code a} nor {@code cc}, and the premise names only {@code b}. */
    @Test
    void thePremiseIsSummedForTheRestsItNamesAPositionOfAndNoOther() {
        assertEquals(2, sumsTakenAskingEveryRest(0));
    }
}
