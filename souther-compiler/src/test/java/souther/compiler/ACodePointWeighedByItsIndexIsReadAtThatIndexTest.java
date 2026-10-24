package souther.compiler;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.IntPredicate;
import java.util.function.ToIntFunction;

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
 * A total over the code points of a string whose weight turns on where each one stands is read
 * code point by code point, where the string's rules settle how many it holds, and a row on each
 * side of a rule about it is a string of the format.
 *
 * <p>Held by running the rows. Each row composed for a rule is put back as an example, answered
 * with what the rule works out to over the string the row holds — worked out here, from the digits
 * and the weights written in the model — so a row whose string does not leave what it was composed
 * for is an example the model answers otherwise, which is an error of the run. The models vary the
 * weights, their period, whether the walk is of the code points reversed or cut, how long the
 * string is, and whether the list is bound to a name.
 */
class ACodePointWeighedByItsIndexIsReadAtThatIndexTest {

    private static final String DIGIT = """
            let digitValue (c: Int): Int =
                match List.get(0, String.codePoints("0")) with
                    | Some zero -> c - zero
                    | None -> unreachable "a one-character string has a first code point"
            """;

    private static String model(String format, String total, String rule) {
        return """
                module p
                data Code = String
                    invariant String.matches("%s", value)
                behavior pick : (c: Code) -> Int
                %s
                let total (code: String): Int = %s
                let pick (c) = {
                    guard %s else 0
                    1
                }
                """.formatted(format, DIGIT, total, rule);
    }

    /** The digits of {@code text}, each its value. */
    private static int[] digits(String text) {
        return text.chars().map(c -> c - '0').toArray();
    }

    /**
     * A model, what the remainder its rule is about comes to of a string of digits — worked out
     * here — and which remainders the rule holds at.
     */
    private record Case(String name, String model, ToIntFunction<String> remainder,
                        IntPredicate rule) {

        int answer(String text) {
            return rule.test(remainder.applyAsInt(text)) ? 1 : 0;
        }
    }

    private static final List<Case> READ = List.of(
            new Case("the weights one and three, from the first",
                    model("[0-9]{13}", """
                            List.sum(List.mapIndexed((i, c) ->
                                (if Int.floorMod(i, 2) == 0 then 1 else 3) * digitValue(c),
                                String.codePoints(code)))""",
                            "Int.floorMod(total(c.value), 10) == 0"),
                    text -> {
                        int[] d = digits(text);
                        int sum = 0;
                        for (int i = 0; i < d.length; i++) {
                            sum += (i % 2 == 0 ? 1 : 3) * d[i];
                        }
                        return Math.floorMod(sum, 10);
                    }, r -> r == 0),
            new Case("the weights the other way round, eight digits, by a name",
                    model("[0-9]{8}", """
                            {
                                let points = String.codePoints(code)
                                List.sum(List.mapIndexed((i, c) ->
                                    (if Int.floorMod(i, 2) == 0 then 3 else 1) * digitValue(c),
                                    points))
                            }""",
                            "Int.floorMod(total(c.value), 10) == 0"),
                    text -> {
                        int[] d = digits(text);
                        int sum = 0;
                        for (int i = 0; i < d.length; i++) {
                            sum += (i % 2 == 0 ? 3 : 1) * d[i];
                        }
                        return Math.floorMod(sum, 10);
                    }, r -> r == 0),
            new Case("a period of three, against seven",
                    model("[0-9]{9}", """
                            List.sum(List.mapIndexed((i, c) ->
                                (if Int.floorMod(i, 3) == 0 then 1
                                 else if Int.floorMod(i, 3) == 1 then 2 else 3) * digitValue(c),
                                String.codePoints(code)))""",
                            "Int.floorMod(total(c.value), 7) >= 4"),
                    text -> {
                        int[] d = digits(text);
                        int sum = 0;
                        for (int i = 0; i < d.length; i++) {
                            sum += (i % 3 + 1) * d[i];
                        }
                        return Math.floorMod(sum, 7);
                    }, r -> r >= 4),
            new Case("weights made of the index, of the first eleven reversed",
                    model("[0-9]{12}", """
                            List.sum(List.mapIndexed((i, c) ->
                                (if i <= 5 then i + 2 else i - 4) * digitValue(c),
                                List.reverse(List.take(11, String.codePoints(code)))))""",
                            "Int.floorMod(total(c.value), 11) <= 1"),
                    text -> {
                        int[] d = digits(text);
                        int sum = 0;
                        for (int k = 0; k < 11; k++) {
                            sum += (k <= 5 ? k + 2 : k - 4) * d[10 - k];
                        }
                        return Math.floorMod(sum, 11);
                    }, r -> r <= 1),
            new Case("the code points from the third on, weighed by where they stand",
                    model("[0-9]{6}", """
                            List.sum(List.mapIndexed((i, c) -> (2 * i + 1) * digitValue(c),
                                List.drop(2, String.codePoints(code))))""",
                            "Int.floorMod(total(c.value), 5) == 3"),
                    text -> {
                        int[] d = digits(text);
                        int sum = 0;
                        for (int k = 0; k < 4; k++) {
                            sum += (2 * k + 1) * d[k + 2];
                        }
                        return Math.floorMod(sum, 5);
                    }, r -> r == 3));

    /** Every model reads its total as a form of the code points at their indices. */
    @Test
    void theTotalIsReadAsAFormOfTheCodePointsAtTheirIndices() {
        for (Case each : READ) {
            String report = report(measured(each.model()));
            assertTrue(report.contains("read as pick/Int.floorMod(")
                            && report.contains("List.get(3, String.codePoints(c))"),
                    () -> each.name() + "\n" + report);
            assertFalse(report.contains("not read:"), () -> each.name() + "\n" + report);
        }
    }

    /** Every rule of each model is composed a row that takes it, and every row is answered as its
     *  string says when it is run. */
    @Test
    void everyRuleIsComposedAStringThatTakesIt() {
        for (Case each : READ) {
            List<String> examples = new ArrayList<>();
            Set<Integer> answers = new TreeSet<>();
            for (List<FixtureTemplate> row : composedForTheRules(measured(each.model()))) {
                String text = textOf(row.getFirst().value());
                assertTrue(text.matches("[0-9]+"), () -> each.name() + ": " + text);
                int answer = each.answer(text);
                answers.add(answer);
                examples.add("    | \"composed " + examples.size() + "\" : ("
                        + row.getFirst().text() + ") -> " + answer);
            }
            assertEquals(Set.of(0, 1), answers,
                    () -> each.name() + ": a row on each side, and not " + examples);
            Compilation answeredBy = Compilation.ofSource(each.model() + "example pick\n"
                    + String.join("\n", examples) + "\n", "Main");
            answeredBy.answerEverything();
            assertEquals(List.of(), answeredBy.errors().stream()
                    .map(error -> error.diagnostic().code() + " " + error.diagnostic().said())
                    .toList(), () -> each.name() + ": each row is answered as its string says: "
                            + examples);
        }
    }

    /**
     * A row at a point of the remainder's line is a string whose remainder is the one its label
     * names, worked out here of its digits: a reading that put a code point at the wrong index, or
     * a weight at the wrong place, writes a string that leaves another.
     */
    @Test
    void aRowAtAPointLeavesTheRemainderItIsFor() {
        for (Case each : READ) {
            Compilation compilation = measured(each.model());
            int checked = 0;
            for (BorderAssessment border : Adequacy.readingsOf(compilation.db(), "p")
                    .get("pick")) {
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
                                if (label.startsWith("Int.floorMod(") && label.contains(") = ")) {
                                    assertEquals(Integer.parseInt(label.substring(
                                                    label.lastIndexOf(' ') + 1)),
                                            each.remainder().applyAsInt(text),
                                            () -> each.name() + ": " + label + " at " + text);
                                    checked++;
                                }
                            }
                        }
                    }
                }
            }
            assertTrue(checked > 0, () -> each.name() + ": some row stands at the line");
        }
    }

    /**
     * Nothing is read code point by code point where the rules leave the string more than one
     * length, where a code point is weighed by itself, or where the walk is cut at a count nothing
     * wrote down: each is a total this does not read, and not one read as numbers apart.
     */
    @Test
    void aTotalThisCannotWriteOutIsLeftUnread() {
        for (String unread : List.of(
                model("[0-9]{12,13}", """
                        List.sum(List.mapIndexed((i, c) ->
                            (if Int.floorMod(i, 2) == 0 then 1 else 3) * digitValue(c),
                            String.codePoints(code)))""",
                        "Int.floorMod(total(c.value), 10) == 0"),
                model("[0-9]{4}", """
                        List.sum(List.mapIndexed((i, c) -> i * digitValue(c) * digitValue(c),
                            String.codePoints(code)))""",
                        "Int.floorMod(total(c.value), 10) == 0"),
                """
                module p
                data Code = String
                    invariant String.matches("[0-9]{6}", value)
                behavior pick : (c: Code, n: Int) -> Int
                let pick (c, n) = {
                    guard Int.floorMod(List.sum(List.mapIndexed((i, x) -> (i + 1) * x,
                        List.take(n, String.codePoints(c.value)))), 10) == 0 else 0
                    1
                }
                """)) {
            String report = report(measured(unread));
            assertFalse(report.contains("List.get("), () -> unread + "\n" + report);
            assertTrue(report.contains("not read:"), () -> unread + "\n" + report);
        }
    }

    /** The rows composed for the decision rules no row takes, each as its inputs. */
    private static List<List<FixtureTemplate>> composedForTheRules(Compilation compilation) {
        List<List<FixtureTemplate>> out = new ArrayList<>();
        Adequacy.generatedOf(compilation.db(), compilation.modules().get(0)).get("pick")
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
