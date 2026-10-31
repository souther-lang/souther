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

    private static final String OVERFLOWS = "9223372036854775807";

    /** A block answering {@code value} that first multiplies a number of the input past what an
     *  {@code Int} holds, and never reads the product. */
    private static String afterAnOverflow(String value) {
        return "{ let unused = String.length(p.value) * " + OVERFLOWS + "\n " + value + " }";
    }

    /** A block answering {@code value} that first works out a sum of two written numbers. */
    private static String afterASafeSum(String value) {
        return "{ let unused = 1 + 1\n " + value + " }";
    }

    /**
     * The least rule that holds a code point of a three-digit string against the remainder a
     * total over the first two leaves: the list, the closure, the map and the divisor are each a
     * hole to put what the case is about in. With nothing put in, the first digit, weighed by the
     * divisor, is apart from the remainder.
     */
    private static String tiny(String codes, String closure, String map, String divisor) {
        return """
                module p
                data Pair = String
                    invariant String.matches("[0-9]{3}", value)
                behavior pick : (p: Pair) -> Int
                let digitValue (c: Int): Int =
                    match List.get(0, String.codePoints("0")) with
                        | Some zero -> c - zero
                        | None -> unreachable "a one-character string has a first code point"
                let pick (p) = {
                    let codes = %s
                    let weighed = %s
                    let r = Int.floorMod(List.sum(weighed), %s)
                    match List.get(2, codes) with
                        | Some c -> if c + r == 55 then 1 else 0
                        | None -> unreachable "three digits"
                }
                """.formatted(codes, map.formatted(closure), divisor);
    }

    private static final String CODES = "String.codePoints(p.value)";
    private static final String CLOSURE = "(i, c) -> (if i == 0 then 7 else 1) * digitValue(c)";
    private static final String MAP = "List.mapIndexed(%s, List.take(2, codes))";
    private static final String DIVISOR = "7";
    private static final String APART =
            "it relates the value here to another value rather than dividing";

    /** Whether the rule is read so that the first digit is shown apart from the remainder. */
    private static boolean readsApart(String codes, String closure, String map, String divisor) {
        return report(measured(tiny(codes, closure, map, divisor))).contains(APART);
    }

    /** The control every case below departs from in one place. */
    @Test
    void theLeastRuleOverTheCodePointsOfAStringIsRead() {
        assertTrue(readsApart(CODES, CLOSURE, MAP, DIVISOR));
    }

    /**
     * What a name, a block or a divisor stands for is a value, and what is worked out to reach
     * it is worked out all the same: the list the closure is applied over, the map a name stands
     * for and the divisor each multiply past what an {@code Int} holds beside the value they
     * come to, and the run ends there. Where what they work out ends no run, the rule is read
     * as it is with the value written in place.
     */
    @Test
    void whatIsWorkedOutToReachAValueIsWorkedOutToo() {
        assertFalse(readsApart(afterAnOverflow(CODES), CLOSURE, MAP, DIVISOR), "the list");
        assertFalse(readsApart(CODES, CLOSURE, afterAnOverflow(MAP), DIVISOR), "the map");
        assertFalse(readsApart(CODES, CLOSURE, MAP, afterAnOverflow(DIVISOR)), "the divisor");
        assertTrue(readsApart(afterASafeSum(CODES), CLOSURE, afterASafeSum(MAP),
                afterASafeSum(DIVISOR)));
    }

    /**
     * That a library call answers whatever it is handed is the call's own, and not its arguments':
     * a count that multiplies past what an {@code Int} holds ends the run, whatever the call then
     * does with the two it comes to.
     */
    @Test
    void aCallThatAnswersWhateverItIsHandedStillWorksOutItsArguments() {
        assertTrue(readsApart(CODES, CLOSURE,
                "List.mapIndexed(%s, List.take(" + afterASafeSum("2") + ", codes))", DIVISOR));
        assertFalse(readsApart(CODES, CLOSURE,
                "List.mapIndexed(%s, List.take(" + afterAnOverflow("2") + ", codes))", DIVISOR));
    }

    /** A closure over code points inside another is read at the arm its match takes too. */
    @Test
    void aClosureOverCodePointsInsideAnotherIsRead() {
        String nested = "(i, c) -> (if i == 0 then 7 else 1) * (digitValue(c) + List.sum("
                + "List.mapIndexed((j, d) -> 0 * digitValue(d), List.take(1, codes))))";
        assertTrue(readsApart(CODES, nested, MAP, DIVISOR));
    }

    /**
     * A remainder is worked out through the number it divides only where the divisor is a
     * positive number written down: by one the run takes from its input, or one that is not
     * positive, working it out may end the run on its own.
     */
    @Test
    void aRemainderByADivisorThatIsNoPositiveConstantIsNotWorkedOutThroughItsDividend() {
        for (String divisor : List.of("0 - 7", "List.length(codes)")) {
            assertFalse(readsApart(CODES, CLOSURE, MAP, divisor), divisor);
        }
    }

    private static String closureMatching(String zeros, String taken) {
        return """
                (i, c) -> (if i == 0 then 7 else 1) * (%s)""".formatted("""
                { let zeros = %s
                  match List.get(0, zeros) with
                      | Some zero -> %s
                      | None -> unreachable "a one-character string has a first code point" }"""
                .formatted(zeros, taken));
    }

    /**
     * A match in the closure is read at the arm a lookup in a list written down takes, and what
     * is worked out to build that list, and the arm taken, end no run; the arm not taken is not
     * asked. A lookup that finds nothing takes neither arm.
     */
    @Test
    void aMatchIsReadAtItsArmOnlyWhereWhatDecidesItAndTheArmTakenEndNoRun() {
        String plain = "String.codePoints(\"0\")";
        assertTrue(readsApart(CODES, closureMatching(plain, "c - zero"), MAP, DIVISOR));
        for (String unsafe : List.of(
                closureMatching("{ let unused = c * " + OVERFLOWS + "\n " + plain + " }",
                        "c - zero"),
                closureMatching(plain, "c * " + OVERFLOWS + " - zero"),
                closureMatching(plain, "c - zero").replace("List.get(0,", "List.get(1,"))) {
            assertFalse(readsApart(CODES, unsafe, MAP, DIVISOR), unsafe);
        }
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
