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

            behavior everyMarkHolds : (marks: List<Int>, flagged: Bool) -> Approved | Asked
            let everyMarkHolds (marks, flagged) =
                if List.all(m -> true, marks) || flagged then Approved else Asked

            behavior noMarkHolds : (marks: List<Int>, flagged: Bool) -> Approved | Asked
            let noMarkHolds (marks, flagged) =
                if List.any(m -> false, marks) || flagged then Approved else Asked

            behavior someMarkHolds : (marks: List<Int>, flagged: Bool) -> Approved | Asked
            let someMarkHolds (marks, flagged) =
                if List.any(m -> true, marks) || flagged then Approved else Asked

            behavior everyMarkFails : (marks: List<Int>, flagged: Bool) -> Approved | Asked
            let everyMarkFails (marks, flagged) =
                if List.all(m -> false, marks) || flagged then Approved else Asked

            behavior writtenMarks : (r: Request, flagged: Bool) -> Approved | Asked
            let writtenMarks (r, flagged) =
                if List.any(m -> m > 3, [ 1, 5 ]) || flagged then Approved else Asked

            behavior noneKept : (marks: List<Int>, flagged: Bool) -> Approved | Asked
            let noneKept (marks, flagged) =
                if List.isEmpty(List.filter(m -> false, marks)) || flagged then Approved
                else Asked
            """;

    /**
     * A predicate fixed at one answer carries that answer through what the operation does with
     * it: every element holding what always holds is true whatever the list, some element holding
     * what never does is false, and the other two are whether the list holds anything.
     */
    @Test
    void aPredicateFixedAtOneAnswerIsCarriedThroughTheOperation() {
        assertEquals(List.of(1, 0), ruleCountAndTheFlag("everyMarkHolds"),
                "every element holding what always holds settles the condition");
        assertEquals(List.of(2, 2), ruleCountAndTheFlag("noMarkHolds"),
                "some element holding what never holds is the flag alone");
        assertEquals(List.of(3, 2), ruleCountAndTheFlag("someMarkHolds"),
                "some element holding what always holds is whether there is one");
        assertEquals(List.of(3, 2), ruleCountAndTheFlag("everyMarkFails"),
                "every element holding what never holds is whether there is none");
        assertEquals(List.of(1, 0), ruleCountAndTheFlag("noneKept"),
                "nothing is kept by what never holds, so the list kept is always empty");
    }

    /**
     * A predicate over a list written out that reads nothing but its element answers the same
     * every time, and is no way out the other way round; one that reads the input beside its
     * element still varies with the input, which `either` holds.
     */
    @Test
    void aPredicateOverAWrittenListReadingOnlyItsElementIsTheSameEveryTime() {
        assertEquals(2, DecisionReadings.readToTheEnd(MODEL, "writtenMarks").size(),
                "neither way of the fixed part is a rule, and the way past it is one");
    }

    /** How many rules, and how many of them turn on the flag. */
    private static List<Integer> ruleCountAndTheFlag(String behavior) {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(MODEL, behavior);
        return List.of(rules.size(),
                (int) rules.stream().filter(rule -> turnsOnTheFlag(rule)).count());
    }

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
