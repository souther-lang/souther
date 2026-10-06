package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A truth one of the language's operations answers is a way through the condition it is a part
 * of, where its answer may be either.
 *
 * <p>Read as a value nothing named, such a part was no way at all: {@code a || List.isEmpty(xs)}
 * was the fork's two arms, and the rules the body draws by the second part went with it. Read as
 * coming out either way, each part of the condition is a distinction a rule turns on — and only
 * where the answer may be either, since an operation applied to what is written out answers the
 * same every time.
 */
class ATruthAnOperationAnswersIsAWayThroughWhatItIsPartOfTest {

    private static final String MODEL = """
            module probe.through

            data High
            data Low
            data Reason = High | Low

            data Request = { cost: Int, nights: Int }
                invariant cost >= 0 && cost <= 1000 && nights >= 0 && nights <= 30

            data Approved
            data Asked

            let applies (r: Request, reason: Reason): Bool =
                match reason with
                    | High -> r.cost > 500
                    | Low -> r.nights > 7

            let reasonsFor (r: Request): List<Reason> =
                List.filter(x -> applies(r, x), [ High, Low ])

            behavior either : (r: Request, flagged: Bool) -> Approved | Asked
            let either (r, flagged) =
                if r.cost > 900 || List.isEmpty(reasonsFor(r)) || flagged then Approved else Asked

            behavior written : (r: Request, flagged: Bool) -> Approved | Asked
            let written (r, flagged) =
                if r.cost > 900 || List.isEmpty([ High ]) || flagged then Approved else Asked

            behavior folded : (r: Request, flagged: Bool) -> Approved | Asked
            let folded (r, flagged) =
                if r.cost > 900 || String.contains("w", "w-1") || flagged then Approved
                else Asked

            behavior unsaid : (r: Request, flagged: Bool) -> Approved | Asked
            let unsaid (r, flagged) =
                if r.cost > 900 || List.contains(High, [ High ]) || flagged then Approved
                else Asked
            """;

    /** Three parts, each a way the condition comes out true, and the way none of them does. */
    @Test
    void eachPartOfTheConditionIsADistinction() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(MODEL, "either");
        assertEquals(4, rules.size(), () -> "a rule per part that settles it, and one for none: "
                + rules);
        assertEquals(List.of(1, 2, 3, 3),
                rules.stream().map(rule -> rule.inOrder().size()).sorted().toList(),
                "each rule turns on the parts before the one that settled it");
    }

    /**
     * A list written out with an element in it is never empty, so the way goes past that part the
     * one way it comes out — and on to the part after it, which comes out both ways.
     */
    @Test
    void aPartFixedAtFalseIsPassedTheWayItComesOut() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(MODEL, "written");
        assertEquals(3, rules.size(), () -> "the first part, then the last part either way: "
                + rules);
    }

    /** A part the checker folds to true settles the condition there, so nothing after it is a
     *  way. */
    @Test
    void aPartFixedAtTrueSettlesTheConditionThere() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(MODEL, "folded");
        assertEquals(2, rules.size(), () -> "the first part, and the folded part: " + rules);
        assertEquals(List.of(), rules.stream().filter(rule -> turnsOnTheFlag(rule)).toList(),
                "no way reaches the part after one that is always true");
    }

    private static boolean turnsOnTheFlag(DecisionRule rule) {
        return rule.inOrder().stream()
                .anyMatch(each -> each.condition().toString().contains("flagged"));
    }

    /**
     * A part the same whatever the input, whose answer this reading cannot name, is stood behind
     * neither way: what the tree reads of a value it cannot witness, and never a way out of it
     * that no row takes.
     */
    @Test
    void aPartFixedAtAnAnswerNobodyNamesIsNeitherWay() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(MODEL, "unsaid");
        assertEquals(2, rules.size(), () -> "the first part, and one way past the rest: "
                + rules);
        assertTrue(rules.stream().anyMatch(rule -> turnsOnTheFlag(rule)),
                () -> "and that way goes on to the part after it: " + rules);
    }
}
