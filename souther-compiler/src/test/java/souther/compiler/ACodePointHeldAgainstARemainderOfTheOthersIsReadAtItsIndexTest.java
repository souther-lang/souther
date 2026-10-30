package souther.compiler;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ComposedRows;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A code point a lookup picks out of a string's code points, held against what a remainder of a
 * total over the others works out to, is read as the code point at its index, and the rule is read
 * as the lines it holds where the string's format shows the code point apart from the total.
 *
 * <p>The model is a check digit: the twelfth digit against eleven less what the first eleven,
 * reversed and weighed by where each stands, leave divided by eleven, nought where that is nought
 * or one. Held by running the rows: each row composed for a rule is run through the module and
 * held to what the check works out to over its string here, and a row at a point of a line
 * is a string whose numbers are the ones its label names, worked out here of its digits.
 *
 * <p>Apart only where the format shows it. Where the format ties the code point to one the total
 * is made of, the remainder the others leave is not every remainder whatever the code point is, and
 * the rule is not read as though the two were apart.
 */
class ACodePointHeldAgainstARemainderOfTheOthersIsReadAtItsIndexTest {

    private static final String MODEL = """
            module p
            data MyNumber = String
                invariant String.matches("[0-9]{12}", value)
            behavior verify : (number: MyNumber) -> Int
            let digitValue (c: Int): Int =
                match List.get(0, String.codePoints("0")) with
                    | Some zero -> c - zero
                    | None -> unreachable "a one-character string has a first code point"
            let weightedSum (body: List<Int>): Int =
                List.sum(List.mapIndexed((i, c) -> (if i <= 5 then i + 2 else i - 4) * digitValue(c),
                                         List.reverse(body)))
            let expectedCheckDigit (body: List<Int>): Int = {
                let r = Int.floorMod(weightedSum(body), 11)
                if r <= 1 then 0 else 11 - r
            }
            let verify (number) = {
                let codes = String.codePoints(number.value)
                let body = List.take(11, codes)
                match List.get(0, List.drop(11, codes)) with
                    | Some c -> if digitValue(c) == expectedCheckDigit(body) then 1 else 0
                    | None   -> unreachable "twelve digits"
            }
            """;

    /** What the first eleven digits of {@code text}, reversed and weighed, leave divided by
     *  eleven. */
    private static int remainderOf(String text) {
        int sum = 0;
        for (int k = 0; k < 11; k++) {
            sum += (k <= 5 ? k + 2 : k - 4) * (text.charAt(10 - k) - '0');
        }
        return Math.floorMod(sum, 11);
    }

    private static int answer(String text) {
        int r = remainderOf(text);
        return text.charAt(11) - '0' == (r <= 1 ? 0 : 11 - r) ? 1 : 0;
    }

    /**
     * The check digit is read as the code point at its index against the remainder, and its
     * lines are drawn. The closure is read once per code point, at the place the code point
     * stands at in the reversed list and with the position it is handed, so that a run gets
     * through the weighed sum is shown.
     */
    @Test
    void theCheckIsReadAsTheCodePointAtItsIndexAgainstTheRemainder() {
        String report = report(measured(MODEL));
        assertFalse(report.contains("not read:"), report);
        assertTrue(report.contains("List.get(11, String.codePoints(number)): = 48"), report);
        assertTrue(report.contains(") + List.get(11, String.codePoints(number)): = 59"), report);
    }

    /**
     * A point of the line on the remainder and the code point added up is composed at a remainder
     * the way to it leaves: past {@code r <= 1}, a row at the sum one below the line holds a
     * remainder of two or more, and the code point what the sum leaves of it.
     */
    @Test
    void aPointOfTheSumIsComposedAtARemainderTheWayLeaves() {
        for (String line : report(measured(MODEL)).lines().toList()) {
            if (line.contains(") + List.get(11, String.codePoints(number)):")) {
                assertFalse(line.contains("no row composed"), line);
            }
        }
    }

    @Test
    void everyRuleIsComposedAStringThatTakesIt() {
        Compilation compilation = measured(MODEL);
        Set<Integer> answers = new TreeSet<>();
        for (List<FixtureTemplate> row : composedForTheRules(compilation)) {
            String text = textOf(row.getFirst().value());
            assertTrue(text.matches("[0-9]{12}"), text);
            answers.add(answer(text));
            assertEquals(new AnswerObservation.Answered(new ObservedValue.Integer(answer(text))),
                    ComposedRows.answer(compilation, "verify", row),
                    () -> text + " is answered as its string says");
        }
        assertEquals(Set.of(0, 1), answers, () -> "a row on each side, and not " + answers);
    }

    private static final Pattern AT = Pattern.compile(" = (\\d+)$");

    /**
     * A row at a point of a line is a string whose numbers come to what its label names: the code
     * point at the index, the remainder, or the two added up.
     */
    @Test
    void aRowAtAPointIsAtTheNumbersItsLabelNames() {
        Compilation compilation = measured(MODEL);
        int checked = 0;
        for (BorderAssessment border : Adequacy.readingsOf(compilation.db(), "p").get("verify")) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (!(attempt instanceof ItemAssessment.Attempt.Certified certified)) {
                        continue;
                    }
                    String written = certified.row().inputs().getFirst().text();
                    String text = written.substring(written.indexOf('"') + 1,
                            written.lastIndexOf('"'));
                    for (var purpose : certified.row().purposes()) {
                        for (String label : purpose.labels()) {
                            Matcher at = AT.matcher(label);
                            if (!at.find()) {
                                continue;
                            }
                            boolean remainder = label.startsWith("Int.floorMod(");
                            boolean codePoint = label.contains(
                                    "List.get(11, String.codePoints(number))");
                            int worked = (remainder ? remainderOf(text) : 0)
                                    + (codePoint ? text.charAt(11) : 0);
                            assertEquals(Integer.parseInt(at.group(1)), worked,
                                    () -> label + " at " + text);
                            checked++;
                        }
                    }
                }
            }
        }
        assertTrue(checked > 0, "some row stands at a point");
    }

    /**
     * Where the format ties the code point held against the remainder to the one the remainder
     * turns on — the last two digits are one digit twice, and the first is weighed by the divisor
     * — the remainder is not every remainder at each value of the code point, and the rule is not
     * read as relating two values apart. With the digits free it is.
     */
    @Test
    void aCodePointTheFormatTiesToTheTotalIsNotTakenApartFromIt() {
        String tied = pair("[0-9](00|11|22|33|44|55|66|77|88|99)");
        String free = pair("[0-9]{3}");
        String apart = "it relates the value here to another value rather than dividing";
        assertFalse(report(measured(tied)).contains(apart), () -> report(measured(tied)));
        assertTrue(report(measured(tied)).contains("not shown to reach every value"),
                () -> report(measured(tied)));
        assertTrue(report(measured(free)).contains(apart), () -> report(measured(free)));
    }

    /**
     * Which code point the closure is handed at each place is read off the string's length, so
     * where the format leaves the length open the applications are not written out and the rule
     * is not read.
     */
    @Test
    void aStringWhoseLengthTheFormatLeavesOpenIsNotWrittenOutCodePointByCodePoint() {
        String open = report(measured(pair("[0-9]{3,5}")));
        assertTrue(open.contains("not read:"), open);
        assertFalse(open.contains("it relates the value here to another value rather than"
                + " dividing"), open);
    }

    private static final String MODEL_WITH_REBUILT_CODES = MODEL.replace(
            "let body = List.take(11, codes)", """
                    let rebuilt = {
                        let unused = List.length(codes) * 9223372036854775807
                        codes
                    }
                    let body = List.take(11, rebuilt)""");

    /**
     * What builds the list the closure is applied over is worked out all the same. The list is
     * the string's code points whatever else the block that answers it computes, but that block
     * multiplies past what an {@code Int} holds, so a run through it does not get through.
     */
    @Test
    void whatBuildsTheListTheClosureIsAppliedOverIsWorkedOutToo() {
        String report = report(measured(MODEL_WITH_REBUILT_CODES));
        assertTrue(report.contains("not read:"), report);
    }

    private static final String MODEL_WITH_A_NAMED_MAP = MODEL.replaceFirst(
            "(?s)let weightedSum.*?\\n(let expectedCheckDigit)", """
                    let weightedSum (body: List<Int>): Int = {
                        let weighed = List.mapIndexed(
                            (i, c) -> (if i <= 5 then i + 2 else i - 4) * digitValue(c),
                            List.reverse(body))
                        List.sum(weighed)
                    }
                    $1""");

    /** The total of a map bound to a name is read as the total of the map written in place. */
    @Test
    void aMapBoundToANameIsReadAsTheMapWrittenInPlace() {
        assertTrue(!MODEL_WITH_A_NAMED_MAP.equals(MODEL));
        assertFalse(report(measured(MODEL_WITH_A_NAMED_MAP)).contains("not read:"),
                () -> report(measured(MODEL_WITH_A_NAMED_MAP)));
    }

    /** Two closures over code points, one inside the other, are each read at the arm their
     *  match takes. Each is read by a reading of its own, so the inner one cannot turn off what
     *  the outer one is read with; this holds the two together. */
    @Test
    void aClosureOverCodePointsInsideAnotherIsReadAtItsArmToo() {
        String nested = MODEL.replace("* digitValue(c)", "* (digitValue(c) + List.sum("
                + "List.mapIndexed((j, d) -> 0 * digitValue(d), List.take(1, body))))");
        assertTrue(!nested.equals(MODEL));
        assertFalse(report(measured(nested)).contains("not read:"),
                () -> report(measured(nested)));
    }

    /**
     * A remainder is worked out through the number it divides only where the divisor is a
     * positive number written down. By a divisor the run takes from its input, or one that is
     * not positive, working it out may end the run on its own, and what the weighed sum ends is
     * not every operation the run works out.
     */
    @Test
    void aRemainderByADivisorThatIsNoPositiveConstantIsNotWorkedOutThroughItsDividend() {
        for (String divisor : List.of("0 - 11", "List.length(body)")) {
            String model = MODEL.replace("Int.floorMod(weightedSum(body), 11)",
                    "Int.floorMod(weightedSum(body), " + divisor + ")");
            assertTrue(!model.equals(MODEL));
            assertTrue(report(measured(model)).contains("not read:"),
                    () -> divisor + "\n" + report(measured(model)));
        }
    }

    /**
     * A match inside the closure is read at its taken arm only where the lookup it matches on
     * finds an element. A lookup past the end of the one-character text finds none, so neither arm
     * is the taken one, the {@code unreachable} one is not excluded, and what the closure works out
     * is not shown to get through.
     */
    @Test
    void aMatchWhoseLookupFindsNothingLeavesTheClosureUnshown() {
        String report = report(measured(MODEL.replace("List.get(0, String.codePoints(\"0\"))",
                "List.get(1, String.codePoints(\"0\"))")));
        assertTrue(report.contains("not read:"), report);
    }

    /**
     * A remainder is shown reached only by strings that are values. The second digit six, and
     * with it the remainder five, stands only before a letter and a combining acute, which a
     * {@code String} holds as one code point and the format then refuses: no value leaves five,
     * and the code point held against the remainder is not taken apart from it. Its sequences
     * read as written, the same format would show every remainder.
     */
    @Test
    void aRemainderOnlyASequenceNoValueIsLeavesIsNotTakenToBeLeft() {
        String apart = "it relates the value here to another value rather than dividing";
        String nfc = report(measured(pair("[0-9][0-5][0-9]bb|[0-9]6[0-9]a\\\\x{301}")));
        assertFalse(nfc.contains(apart), nfc);
        assertTrue(nfc.contains("not shown to reach every value"), nfc);
        // Read as written, no value is refused, and the same format shows every remainder.
        String written = report(measured(pair("[0-9][0-5][0-9]bb|[0-9]6[0-9]ab")));
        assertTrue(written.contains(apart), written);
        // A dot above after a digit joins nothing, so the string is a value whose third code point
        // is the dot, and the remainder beside it five alone: whatever the code point is is asked
        // of every value, the ones read as written or not.
        String marked = report(measured(pair("[0-9][0-6][0-9]bb|[0-9]6\\\\x{307}bb")));
        assertFalse(marked.contains(apart), marked);
    }

    /**
     * A code point is taken to take only what a value holds at its index. The format places a
     * letter first in a letter and a combining acute, which a {@code String} holds as one code
     * point and the format then refuses, so the only string of two is {@code bb}: the code point is
     * ninety-eight and nothing else, and a number held against it is not shown to have rows on
     * both sides of ninety-seven.
     */
    @Test
    void aCodePointOnlyASequenceNoValueIsPlacesIsNotTakenToBeTaken() {
        String report = report(measured("""
                module nfc
                data Two = String
                    invariant String.matches("a\\\\x{301}|bb", value)
                behavior atLeast : (s: Two, n: Int) -> Int
                let atLeast (s, n) =
                    match List.get(0, String.codePoints(s.value)) with
                        | Some c -> if n >= c then 1 else 0
                        | None -> 2
                """));
        assertFalse(report.contains("relates the value here to another value rather than dividing"
                + " the values here, about `n`"), report);
        assertTrue(report.contains("not shown to reach every value here, so which values here"
                + " settle it on their own is not worked out, about `n`"), report);
    }

    private static String pair(String format) {
        return """
                module p
                data Pair = String
                    invariant String.matches("%s", value)
                behavior pick : (p: Pair) -> Int
                let pick (p) = {
                    let codes = String.codePoints(p.value)
                    let r = Int.floorMod(List.sum(List.mapIndexed((i, x) ->
                        (if i == 0 then 7 else 1) * x, List.take(2, codes))), 7)
                    match List.get(2, codes) with
                        | Some c -> if c + r == 55 then 1 else 0
                        | None -> unreachable "three digits"
                }
                """.formatted(format);
    }

    /** The rows composed for the decision rules no row takes, each as its inputs. */
    private static List<List<FixtureTemplate>> composedForTheRules(Compilation compilation) {
        List<List<FixtureTemplate>> out = new ArrayList<>();
        Adequacy.generatedOf(compilation.db(), compilation.modules().get(0)).get("verify")
                .generation().stream()
                .filter(each -> each.finding().about() instanceof About.ARuleNoRowTakes)
                .forEach(each -> {
                    if (each.outcome() instanceof GenerationOutcome.Generated made) {
                        made.candidates().forEach(row -> out.add(row.inputs()));
                    }
                });
        return out;
    }

    /** The text {@code value} writes, under whatever names it wears. */
    private static String textOf(Hir.Expr value) {
        return switch (value) {
            case Hir.StringLit text -> text.value();
            case Hir.Apply applied when applied.args().size() == 1 ->
                    textOf(applied.args().getFirst());
            default -> throw new AssertionError("a text: " + value);
        };
    }

    /** Each model measured once for the class: the methods read the same models, and only read
     *  them. */
    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static Compilation measured(String source) {
        return MEASURED.computeIfAbsent(source, text -> {
            Compilation compilation = Compilation.ofSource(text, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            return compilation;
        });
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
