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
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
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
 * or one. Held by running the rows: each row composed for a rule is put back as an example,
 * answered with what the check works out to over its string here, and a row at a point of a line
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
        List<String> examples = new ArrayList<>();
        Set<Integer> answers = new TreeSet<>();
        for (List<FixtureTemplate> row : composedForTheRules(measured(MODEL))) {
            String text = textOf(row.getFirst().value());
            assertTrue(text.matches("[0-9]{12}"), text);
            answers.add(answer(text));
            examples.add("    | \"composed " + examples.size() + "\" : (" + row.getFirst().text()
                    + ") -> " + answer(text));
        }
        assertEquals(Set.of(0, 1), answers, () -> "a row on each side, and not " + examples);
        Compilation answeredBy = Compilation.ofSource(MODEL + "example verify\n"
                + String.join("\n", examples) + "\n", "Main");
        answeredBy.answerEverything();
        assertEquals(List.of(), answeredBy.errors().stream()
                .map(error -> error.diagnostic().code() + " " + error.diagnostic().said())
                .toList(), () -> "each row is answered as its string says: " + examples);
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
