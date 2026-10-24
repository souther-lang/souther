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

    /** A total that stays in the range of {@code Int} while a product on the way does not: "A" is
     *  65, whose total is the limit asked for and whose product is past the range, so the model
     *  aborts on it. A row holding it is one no answer of the total's can be given to. */
    private static final String PAST_THE_RANGE_ON_THE_WAY = """
            module p
            behavior pick : (s: String) -> Int
            let pick (s) = {
                guard List.sum(List.map((x) -> 200000000000000000 * x - 4000000000000000000,
                        String.codePoints(s))) >= 9000000000000000000 else 0
                1
            }
            """;

    /** Each model, with what its condition works out to over the string a row holds and the
     *  answers some row of it is composed for. */
    private static final Map<String, Function<String, Integer>> ANSWERED = Map.of(
            PAST_THE_RANGE_ON_THE_WAY, text -> text.codePoints().mapToObj(BigInteger::valueOf)
                    .map(point -> point.multiply(BigInteger.valueOf(200000000000000000L))
                            .subtract(new BigInteger("4000000000000000000")))
                    .reduce(BigInteger.ZERO, BigInteger::add)
                    .compareTo(new BigInteger("9000000000000000000")) >= 0 ? 1 : 0,
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
            PAST_THE_RANGE_ON_THE_WAY, Set.of(0),
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
        ANSWERED.forEach((model, by) -> composedAndAnswered(model, by, COMPOSED_FOR.get(model)));
    }

    /**
     * Where the type holds its strings to a format, the strings coming to the number are ones it
     * holds: thirteen digits come to no less than 624 and no more than 741, so a string of the
     * format is on each side of 700, and a string written plainly and moved to the number is one
     * the format refuses. The format that loops reaches 700 only past twelve digits.
     */
    @Test
    void aStringComingToTheNumberIsOneItsTypeHolds() {
        for (String rule : List.of("String.matches(\"[0-9]{13}\", value)",
                "String.matches(\"[0-9]+\", value)")) {
            composedAndAnswered("""
                    module p
                    data Code = String
                        invariant %s
                    behavior pick : (c: Code) -> Int
                    let pick (c) = {
                        guard List.sum(String.codePoints(c.value)) >= 700 else 0
                        1
                    }
                    """.formatted(rule), text -> sumOf(text) >= 700 ? 1 : 0, Set.of(0, 1));
        }
    }

    /**
     * A rule on what a division leaves of what the code points of a formatted string come to has a
     * row on each side: a string of the format whose sum leaves the remainder asked for, and one
     * whose sum does not. Thirteen digits come to no less than 624, so a sum of the class nearest
     * nought is no sum any of them comes to.
     */
    @Test
    void aRemainderOfWhatTheCodePointsComeToIsComposedAStringOfTheFormat() {
        composedAndAnswered("""
                module p
                data Code = String
                    invariant String.matches("[0-9]{13}", value)
                behavior pick : (c: Code) -> Int
                let pick (c) = {
                    guard Int.floorMod(List.sum(String.codePoints(c.value)), 10) == 0 else 0
                    1
                }
                """, text -> Math.floorMod(sumOf(text), 10) == 0 ? 1 : 0, Set.of(0, 1));
        // A digit's value is its code point less 48, so the total is the code points' less 48 for
        // each: two numbers of the string, the second of which is the length the format holds.
        composedAndAnswered("""
                module p
                data Code = String
                    invariant String.matches("[0-9]{13}", value)
                behavior pick : (c: Code) -> Int
                let pick (c) = {
                    guard Int.floorMod(List.sum(List.map((x) -> x - 48,
                        String.codePoints(c.value))), 10) == 0 else 0
                    1
                }
                """, text -> Math.floorMod(sumOf(text) - 48 * lengthOf(text), 10) == 0 ? 1 : 0,
                Set.of(0, 1));
    }

    /** The rows composed for {@code model}'s rules, answered as {@code by} works them out and run:
     *  {@code expected} are the answers some row is composed for. */
    private static void composedAndAnswered(String model, Function<String, Integer> by,
                                            Set<Integer> expected) {
        List<String> examples = new ArrayList<>();
        Set<Integer> answers = new TreeSet<>();
        for (List<FixtureTemplate> row : composedForTheRules(measured(model))) {
            int answer = by.apply(textOf(row.getFirst().value()));
            answers.add(answer);
            examples.add("    | \"composed " + examples.size() + "\" : ("
                    + row.getFirst().text() + ") -> " + answer);
        }
        assertEquals(expected, answers,
                () -> "a row for every rule some string takes: " + examples + "\n" + model);

        // Run and not measured: an example whose answer is not the program's is an error, which
        // is all this asks of the rows.
        Compilation answeredBy = Compilation.ofSource(model + "example pick\n"
                + String.join("\n", examples) + "\n", "Main");
        answeredBy.answerEverything();
        assertEquals(List.of(), answeredBy.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                .toList(), () -> "each row is answered as its string says: " + examples);
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

    /**
     * A digit's value read off the code point of {@code "0"}, as a lookup in the code points of a
     * written string, is the same weighing as the number written down: the arm taking a present
     * option is the one every element takes, whichever order the arms are in and whether the
     * match is in a helper or in the closure.
     */
    @Test
    void aLookupInWrittenCodePointsIsTheNumberItPicks() {
        for (String closure : List.of(
                "(x) -> x - 48",
                """
                (x) -> match List.get(0, String.codePoints("0")) with
                        | Some zero -> x - zero
                        | None -> 0""",
                """
                (x) -> match List.get(0, String.codePoints("0")) with
                        | None -> 0
                        | Some zero -> x - zero""",
                "(x) -> digit(x)")) {
            String report = report(measured("""
                    module p
                    behavior pick : (s: String) -> Int
                    let digit (c: Int): Int =
                        match List.get(0, String.codePoints("0")) with
                            | Some zero -> c - zero
                            | None -> unreachable "a one-character string has a first code point"
                    let pick (s) = {
                        guard List.sum(List.map(%s, String.codePoints(s))) >= 10 else 0
                        1
                    }
                    """.formatted(closure)));
            assertTrue(report.contains("read as pick/List.sum(String.codePoints(s))"
                    + " - 48 * String.length(s): = 10"), () -> closure + "\n" + report);
        }
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

    /** Where a total is in the range of {@code Int} and a product on the way is not, the model
     *  aborts: "A" is 65, whose total is the limit asked for and whose product is past the range,
     *  so no answer holds of it. "-(" has the same total with every product in range, and the
     *  model answers 1. What the rows composed for it are says what the compiler wrote, not what
     *  a string can do: it is silent on "-(" and says so, it does not say there is none. */
    @Test
    void aProductPastTheRangeAbortsWhereAnInRangeStringWithTheSameTotalAnswers() {
        String model = PAST_THE_RANGE_ON_THE_WAY;
        assertEquals(List.of(), errorsOf(model, "\"-(\"", 1), () -> "\"-(\" answers 1");
        assertEquals(1, errorsOf(model, "\"-(\"", 0).size(), () -> "and not 0");
        // An abort is no answer: of an `Int` answer that is 0 or 1, neither holds.
        assertEquals(1, errorsOf(model, "\"A\"", 0).size(), () -> "\"A\" does not answer 0");
        assertEquals(1, errorsOf(model, "\"A\"", 1).size(), () -> "and does not answer 1");

        String report = report(measured(model));
        assertTrue(report.contains("nothing could show a row can be written at a decision rule"),
                () -> "a rule no row was composed for is undecided: " + report);
    }

    /** The errors of {@code model} given one example, the string {@code literal} answering
     *  {@code answer}. */
    private static List<String> errorsOf(String model, String literal, int answer) {
        Compilation compilation = Compilation.ofSource(model + "example pick\n    | \"fixed\" : ("
                + literal + ") -> " + answer + "\n", "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList();
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
