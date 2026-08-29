package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OwedBoundaryPoint;
import souther.compiler.report.AdequacyReport;

import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule written inside a step a combinator applies per element is a line, with the points a row has
 * to meet it at.
 *
 * <p>How many times a run passes a comparison used to settle this, and what it settles now is the
 * arithmetic. A line is over positions of the input and nothing else, so a run through a comparison
 * that bears one reads what the row holds however many times it passes: at one occurrence of a
 * position where the passes stand at different occurrences of one, and at the same values where they
 * do not.
 *
 * <p>Which is why the first of these is here. Nothing about an element enters its rule at all, and
 * it was refused for standing where an element's rule stands — so it is the case that says what the
 * refusal was costing, with none of the reading of elements in it.
 */
class ARuleInsideAWalkOverAWrittenListIsALineWithPointsTest {

    /**
     * The line and the four points a row is owed at it.
     *
     * <p>The rule is {@code n >= 100000} over an {@code Int}, so a row stands on the line at a
     * hundred thousand, off it at the value next to that one, and inside and outside it anywhere
     * past each of those.
     */
    private static final String AT_A_HUNDRED_THOUSAND =
            "[n/x < 100000, n/100000 <= x] unread [] points ["
                    + "classify/n ON 100000, classify/n OFF 99999, "
                    + "classify/n IN 100000 < n, classify/n OUT n < 99999]";

    /** A rule no element enters, written inside a step applied per element of a written list. */
    @Test
    void aRuleNoElementEntersIsALine() {
        assertEquals(AT_A_HUNDRED_THOUSAND, reading("""
                {
                        let ks = [ Big { threshold = 100000 }, Big { threshold = 200000 } ]
                        if List.any((k) -> n >= 100000, ks) then Yes else No
                    }"""));
    }

    /**
     * And so is a rule that compares against a number every element of the list states.
     *
     * <p>The shape a model reaches this by, and the whole of what it takes: the arm leaves one
     * member standing, that member writes a hundred thousand under the field, and the rule is a line
     * there. The list holds a member of another case, which is what makes the arm do work.
     */
    @Test
    void aRuleAgainstANumberEveryElementStatesIsTheSameLine() {
        assertEquals(AT_A_HUNDRED_THOUSAND, reading("""
                {
                        let ks = [ AtMost { threshold = 100000 }, Whatever ]
                        if List.any((k) -> reaches(n, k), ks) then Yes else No
                    }"""));
    }

    /**
     * And a list whose members state two numbers is a rule with no line, as it was.
     *
     * <p>Beside the one above and differing in one number. What tells them apart is what the members
     * state and not how many there are, which case they are, or what the arm admits.
     */
    @Test
    void aRuleAgainstTwoNumbersIsNoLine() {
        assertEquals("[] unread [n UNSUPPORTED_SYNTAX] points []", reading("""
                {
                        let ks = [ AtMost { threshold = 100000 }, AtMost { threshold = 200000 } ]
                        if List.any((k) -> reaches(n, k), ks) then Yes else No
                    }"""));
    }

    /**
     * The model this is about, written the way a model of this size writes it.
     *
     * <p>The candidates come back from a helper, one of them wraps its number in a value type, the
     * arm that admits it is one of three, and the comparison is inside a second helper the first
     * one calls. None of that is a case of its own: it is one reading through the names a model puts
     * between a rule and the value it is written about, and a fixture with the names taken out would
     * be testing a shape nobody writes.
     *
     * <p>Two lines come of it, and the second is why the first is not the whole claim. The arm that
     * admits the candidate holding a value type states a hundred thousand, and the arm that admits
     * the one holding a parameter states that parameter — so what a member contributes is whatever
     * it wrote, and a reading that only ever answered with written numbers would pass the first and
     * fail the second.
     */
    @Test
    void aModelReachesItsThresholdThroughACandidateListAndAnArm() {
        assertEquals("[予定費用/x < 100000, 予定費用/100000 <= x, 役職/x <= 3, 役職/3 < x] "
                        + "unread [] points ["
                        + "判定する/予定費用 ON 100000, 判定する/予定費用 OFF 99999, "
                        + "判定する/予定費用 IN 100000 < 予定費用, 判定する/予定費用 OUT 予定費用 < 99999, "
                        + "判定する/役職 ON 4, 判定する/役職 OFF 3, "
                        + "判定する/役職 IN 4 < 役職, 判定する/役職 OUT 役職 < 3]",
                readingOf("""
                module g

                data 金額 = Int
                data 高額出張 = { 基準金額: 金額 }
                data 権限不足 = { 役職: Int }
                data 先方費用負担
                data 事前承認理由 = 高額出張 | 権限不足 | 先方費用負担
                data Yes
                data No

                let 事前承認理由の候補 (役職: Int): List<事前承認理由> =
                    [ 高額出張 { 基準金額 = 金額(100000) }
                    , 権限不足 { 役職 = 役職 }
                    , 先方費用負担 ]

                let 高額か (予定費用: Int, 基準金額: 金額): Bool = 予定費用 >= 基準金額.value

                let 該当するか (予定費用: Int, 理由: 事前承認理由): Bool =
                    match 理由 with
                        | 高額出張 { 基準金額 } -> 高額か(予定費用, 基準金額)
                        | 権限不足 { 役職 }     -> 役職 > 3
                        | 先方費用負担          -> false

                behavior 判定する : (予定費用: Int, 役職: Int) -> Yes | No
                let 判定する (予定費用, 役職) =
                    if List.any((理由) -> 該当するか(予定費用, 理由), 事前承認理由の候補(役職))
                        then Yes else No

                example 判定する
                    | "one" : (1, 1) -> No
                """, "判定する"));
    }

    /** The classes, what went unread, and the points a row is owed, of {@code classify}. */
    private static String reading(String body) {
        String source = """
                module g

                data Big = { threshold: Int }
                data Yes
                data No

                data AtMost = { threshold: Int }
                data Whatever
                data Reason = AtMost | Whatever

                let reaches (n: Int, reason: Reason): Bool =
                    match reason with
                        | AtMost { threshold } -> n >= threshold
                        | Whatever             -> false

                behavior classify : (n: Int) -> Yes | No
                let classify (n) = %s

                example classify
                    | "one" : (1) -> No
                """.formatted(body);
        return readingOf(source, "classify");
    }

    /** The same, of whichever behavior {@code source} is about. */
    private static String readingOf(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(java.util.List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " "
                        + each.diagnostic().primary()).toList(),
                "the model under test compiles");
        AdequacyReport.BehaviorReport read = AdequacyReport.of(compilation)
                .modules().get(0).behaviors().stream()
                .filter(each -> each.name().equals(behavior)).findFirst().orElseThrow();
        return "[" + read.partition().axes().stream()
                .flatMap(axis -> axis.classes().stream())
                .collect(Collectors.joining(", "))
                + "] unread [" + read.partition().notRead().stream()
                .map(each -> each.at() + " " + each.reason())
                .collect(Collectors.joining(", "))
                + "] points [" + read.partition().owedPoints().stream()
                .map(ARuleInsideAWalkOverAWrittenListIsALineWithPointsTest::said)
                .collect(Collectors.joining(", ")) + "]";
    }

    /** One point a row is owed, as the position, which of the four it is, and the value. */
    private static String said(OwedBoundaryPoint point) {
        return point.axis() + " " + point.role() + " " + point.against();
    }
}
