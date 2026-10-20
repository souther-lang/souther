package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule about what the code points of a string add up to is a rule about a number of that string,
 * as a rule about how long it is: its line is drawn at the string's position, and a row on each
 * side of it is a string written to come to the number there.
 *
 * <p>Held by running the rows. Each row composed for a rule is put back as an example, answered
 * with what the condition works out to over the string the row holds — added up here, apart from
 * anything the compiler read — so a string that does not come to what it was written for is an
 * example the model answers otherwise.
 */
class WhatTheCodePointsOfAStringComeToIsANumberOfTheStringTest {

    /** The total written straight over the list of code points. */
    private static final String STRAIGHT = """
            module p
            behavior pick : (s: String) -> Int
            let pick (s) = {
                guard List.sum(String.codePoints(s)) >= 10 else 0
                1
            }
            """;

    /** The list bound to a name first, which is the same list. */
    private static final String NAMED = """
            module p
            behavior pick : (s: String) -> Int
            let pick (s) = {
                let points = String.codePoints(s)
                guard List.sum(points) >= 10 else 0
                1
            }
            """;

    /** The string inside a name of its own. */
    private static final String UNDER_A_NAME = """
            module p
            data Code = String
            behavior pick : (c: Code) -> Int
            let pick (c) = {
                guard List.sum(String.codePoints(c.value)) >= 10 else 0
                1
            }
            """;

    /** What the code points come to beside how long the string is, which is one string to write
     *  for both. */
    private static final String BESIDE_ITS_LENGTH = """
            module p
            behavior pick : (s: String) -> Int
            let pick (s) = {
                guard String.length(s) >= 2 else 0
                guard List.sum(String.codePoints(s)) <= 200 else 1
                2
            }
            """;

    /** Each code point weighed before the total, which is a multiple of the total. */
    private static final String WEIGHED = """
            module p
            behavior pick : (s: String) -> Int
            let pick (s) = {
                guard List.sum(List.map((x) -> 3 * x, String.codePoints(s))) >= 300 else 0
                1
            }
            """;

    /** Each code point weighed and moved, which is a multiple of the total and of how many there
     *  are. */
    private static final String WEIGHED_AND_MOVED = """
            module p
            behavior pick : (s: String) -> Int
            let pick (s) = {
                let weighed = List.map((x) -> 2 * x + 1, String.codePoints(s))
                guard List.sum(weighed) >= 300 else 0
                1
            }
            """;

    /** A closure that does not turn on the code point: the total is that constant for each one. */
    private static final String SAME_FOR_EACH = """
            module p
            behavior pick : (s: String) -> Int
            let pick (s) = {
                guard List.sum(List.map((x) -> 5, String.codePoints(s))) >= 20 else 0
                1
            }
            """;

    /** A weight at which the product leaves the range of {@code Int} for some code points: a row
     *  holding one is a row the model aborts on, and none may be composed. */
    private static final String NEAR_THE_LIMIT = """
            module p
            behavior pick : (s: String) -> Int
            let pick (s) = {
                guard List.sum(List.map((x) -> 100000000000000000 * x, String.codePoints(s)))
                        >= 9200000000000000000 else 0
                1
            }
            """;

    /** Each model, with what its condition works out to over the string a row holds and the
     *  answers some row of it is composed for. */
    private static final Map<String, Function<String, Integer>> ANSWERED = Map.of(
            NEAR_THE_LIMIT, text -> BigInteger.valueOf(sumOf(text))
                    .multiply(BigInteger.valueOf(100000000000000000L))
                    .compareTo(new BigInteger("9200000000000000000")) >= 0 ? 1 : 0,
            SAME_FOR_EACH, text -> 5 * lengthOf(text) >= 20 ? 1 : 0,
            WEIGHED, text -> 3 * sumOf(text) >= 300 ? 1 : 0,
            WEIGHED_AND_MOVED, text -> 2 * sumOf(text) + lengthOf(text) >= 300 ? 1 : 0,
            STRAIGHT, text -> sumOf(text) >= 10 ? 1 : 0,
            NAMED, text -> sumOf(text) >= 10 ? 1 : 0,
            UNDER_A_NAME, text -> sumOf(text) >= 10 ? 1 : 0,
            BESIDE_ITS_LENGTH, text -> lengthOf(text) < 2 ? 0 : sumOf(text) <= 200 ? 2 : 1);

    private static final Map<String, Set<Integer>> COMPOSED_FOR = Map.of(
            NEAR_THE_LIMIT, Set.of(0, 1),
            SAME_FOR_EACH, Set.of(0, 1),
            WEIGHED, Set.of(0, 1),
            WEIGHED_AND_MOVED, Set.of(0, 1),
            STRAIGHT, Set.of(0, 1),
            NAMED, Set.of(0, 1),
            UNDER_A_NAME, Set.of(0, 1),
            BESIDE_ITS_LENGTH, Set.of(0, 1, 2));

    /** The line is drawn on the string's number, however the list was reached. */
    @Test
    void theLineIsDrawnOnWhatTheStringsCodePointsComeTo() {
        for (String model : List.of(STRAIGHT, NAMED)) {
            String report = report(measured(model));
            assertTrue(report.contains("read as pick/List.sum(String.codePoints(s)): = 10"),
                    () -> report);
            assertTrue(report.contains("read as pick/List.sum(String.codePoints(s)): = 9"),
                    () -> report);
            assertFalse(report.contains("not read:"), () -> report);
        }
    }

    /** Every rule some string takes is composed a row that takes it, and the row is answered as
     *  its string says. */
    @Test
    void everyRuleSomeStringTakesIsComposedARowThatTakesIt() {
        ANSWERED.forEach((model, by) -> {
            List<String> examples = new ArrayList<>();
            Set<Integer> answers = new TreeSet<>();
            for (List<FixtureTemplate> row : composedForTheRules(measured(model))) {
                int answer = by.apply(textOf(row.getFirst().value()));
                answers.add(answer);
                examples.add("    | \"composed " + examples.size() + "\" : ("
                        + row.getFirst().text() + ") -> " + answer);
            }
            assertEquals(COMPOSED_FOR.get(model), answers,
                    () -> "a row for every rule some string takes: " + examples);

            Compilation answeredBy = measured(model + "example pick\n"
                    + String.join("\n", examples) + "\n");            assertEquals(List.of(), answeredBy.errors().stream()
                    .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                    .toList(), () -> "each row is answered as its string says: " + examples);
        });
    }

    /** The total of a weighed code point is a multiple of the total, however far it is carried
     *  into a rule: the remainder of it by a modulus is read of the string's number. */
    @Test
    void aWeighedTotalIsReadInsideAnotherOperation() {
        String report = report(measured("""
                module p
                data Yes = { n: Int }
                data No = { n: Int }
                behavior verify : (s: String) -> Yes | No
                    constructs Yes, No
                let verify (s) =
                    if Int.floorMod(List.sum(List.map((x) -> 3 * x, String.codePoints(s))), 11) <= 1
                    then Yes { n = 0 } else No { n = 0 }
                """));
        assertTrue(report.contains(
                "read as verify/Int.floorMod(3 * List.sum(String.codePoints(s)), 11): = 1"),
                () -> report);
        assertFalse(report.contains("not read:"), () -> report);
    }

    /** A walk whose answer is no term of the total is no weighing of it. {@code sortBy} hands its
     *  closure each code point and keeps the code points: what the closure computes is a key. A
     *  walk that keeps some of them adds up some of them. */
    @Test
    void aWalkThatDoesNotAnswerOneValuePerCodePointIsNotReadAsAWeighing() {
        for (String walk : List.of(
                "List.sortBy((x) -> 3 * x, String.codePoints(s))",
                "List.sortBy((x) -> 0, String.codePoints(s))",
                "List.take(3, List.map((x) -> 3 * x, String.codePoints(s)))",
                "List.filter((x) -> x > 50, String.codePoints(s))")) {
            String report = report(measured("""
                    module p
                    behavior pick : (s: String) -> Int
                    let pick (s) = {
                        guard List.sum(%s) >= 100 else 0
                        1
                    }
                    """.formatted(walk)));
            assertTrue(report.contains("not read:"), () -> walk + "\n" + report);
            assertFalse(report.contains("read as"), () -> walk + "\n" + report);
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

    /** What the code points of {@code text} come to, each the number it is. */
    private static long sumOf(String text) {
        return text.codePoints().asLongStream().sum();
    }

    private static long lengthOf(String text) {
        return text.codePointCount(0, text.length());
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
