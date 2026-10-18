package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison on what {@code Option.withDefault} answers is read as the comparison on the
 * {@code match} the helper is written as.
 *
 * <p>The analysis expands a library operation that nothing states a fact of, so the call and the
 * {@code match} written out are one program to it, and a rule about either draws the same lines.
 */
class AnOptionConsumedByAHelperIsReadAsTheChoiceItIsTest {

    private static String report(String behavior) {
        String source = """
                module m

                data H = { qty: Option<Int>, q: Int }

                %s
                """.formatted(behavior);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String lineAbout(String report, String word) {
        return report.lines().filter(line -> line.contains(word)).findFirst().orElse("");
    }

    @Test
    void aComparisonOnWithDefaultIsReadToTheEnd() {
        String report = report("""
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(0, h.qty) >= 3
                """);

        assertFalse(report.contains("not read"), report);
        assertEquals("complete", measurement(report), report);
    }

    @Test
    void itDrawsTheLinesTheMatchWrittenOutDraws() {
        String called = report("""
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(0, h.qty) >= 3
                """);
        String written = report("""
                behavior f : (h: H) -> Bool
                let f (h) =
                    (match h.qty with
                        | Some v -> v
                        | None -> 0) >= 3
                """);

        assertEquals(lineAbout(written, "border "), lineAbout(called, "border "), called);
        assertEquals(lineAbout(written, "partition "), lineAbout(called, "partition "), called);
    }

    @Test
    void aDefaultAboveTheThresholdKeepsTheNoneSideInTheStatement() {
        String report = report("""
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(5, h.qty) >= 3
                """);

        assertFalse(report.contains("not read"), report);
        assertEquals("complete", measurement(report), report);
    }

    @Test
    void aComparisonAgainstAnotherNumberOfTheInputDrawsALineOnEach() {
        String report = report("""
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(0, h.qty) >= h.q
                """);

        assertEquals("complete", measurement(report), report);
        assertTrue(lineAbout(report, "border ").contains("borders 2"), report);
    }

    @Test
    void theCasesOfASumAreReadAsTheyWere() {
        String report = report("""
                data Small
                data Large
                data Size = Small | Large
                data S = { size: Size, n: Int }

                behavior f : (s: S) -> Bool
                let f (s) =
                    match s.size with
                        | Small -> s.n >= 3
                        | Large -> false
                """);

        assertEquals("complete", measurement(report), report);
        assertTrue(lineAbout(report, "border ").contains("borders 1"), report);
    }

    /**
     * What the helper's own match owes is nothing of the model's.
     *
     * <p>Every point of the line the comparison draws, and the optional absent, are rows here; if
     * reading the helper through put an arm or a rule in the model that nobody wrote, something
     * would be owed that these rows do not answer.
     */
    @Test
    void theRowsTheModelStatesAnswerEverythingTheReadingOwes() {
        Compilation compilation = Compilation.ofSource("""
                module m

                data H = { qty: Option<Int>, q: Int }

                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(0, h.qty) >= 3

                example f
                    | "on the line" : (H { qty = 3, q = 0 }) -> true
                    | "off the line" : (H { qty = 2, q = 0 }) -> false
                    | "in" : (H { qty = 10, q = 0 }) -> true
                    | "out" : (H { qty = -4, q = 0 }) -> false
                    | "absent" : (H { qty = None, q = 0 }) -> false
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertEquals(0, compilation.errors().size(), report);
        assertFalse(report.contains("!"), report);
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    /**
     * The ways through what the helper does are the helper's and not the body's.
     *
     * <p>The match the helper is written as is read through for what the comparison says of the
     * input, and is no decision the model states: the body has the one rule it has with the call
     * standing, and a row is not owed at the optional's two cases.
     */
    @Test
    void theHelpersOwnMatchIsNoDecisionOfTheModel() {
        String report = report("""
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(5, h.qty) >= 3
                """);

        assertTrue(report.contains("decision    rules 1"), report);
        assertTrue(report.contains("branch      not measured (no row names this behavior)"),
                report);
    }

    /** One that the model writes is a decision of the model, read the way it always was. */
    @Test
    void aMatchTheModelWritesIsStillTwoDecisionRules() {
        String report = report("""
                behavior f : (h: H) -> Bool
                let f (h) =
                    (match h.qty with
                        | Some v -> v
                        | None -> 5) >= 3
                """);

        assertTrue(report.contains("decision    rules 2"), report);
    }

    /**
     * An operation answering an option; what the statement turns on to say whether it finds
     * something; a list it finds nothing in; one it finds something in; and what it finds there.
     *
     * <p>What the operation finds is no position of the input, so nothing is said of where it falls:
     * the first element meeting the predicate, the element at the index and the greatest are three
     * different elements, and a row that names {@code xs} names none of them.
     */
    static Stream<Arguments> operationsAnsweringAnOption() {
        return Stream.of(
                Arguments.of("List.find(x -> x > 10, xs)", "xs[*]", "[5]", "[12]", 12),
                Arguments.of("List.get(2, xs)", "List.length(xs)", "[1]", "[1, 2, 3]", 3),
                Arguments.of("List.max(xs)", "List.length(xs)", "[]", "[5]", 5));
    }

    private static String reportOf(String operation, String body, String rows) {
        Compilation compilation = Compilation.ofSource("""
                module p

                behavior f : (xs: List<Int>, q: Int) -> Bool
                let f (xs, q) = %s

                %s
                """.formatted(body.formatted(operation), rows), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(0, compilation.errors().size(), operation);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static final String CALLED = "Option.withDefault(0, %s) >= q";

    private static final String WRITTEN = """
            match %s with
                    | Some v -> v >= q
                    | None -> 0 >= q""";

    /** The points a line on {@code at} is drawn at, as the report reads them, in order. */
    private static List<String> pointsOn(String report, String at) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith("· read as f/" + at + ":"))
                .sorted()
                .toList();
    }

    /** Every line the report says about {@code at}, with which comparison said it left out. */
    private static List<String> saidAbout(String report, String at) {
        return report.lines().map(String::strip)
                .filter(line -> line.endsWith("about `" + at + "`"))
                .map(line -> line.replaceFirst("comparison@\\d+:\\d+", "comparison"))
                .toList();
    }

    /**
     * The line the default draws is drawn where the operation finds nothing, and the value it finds
     * is related to {@code q} as the {@code match} written out relates it.
     */
    @ParameterizedTest
    @MethodSource("operationsAnsweringAnOption")
    void theLineTheDefaultDrawsIsTheOneTheMatchDraws(String operation) {
        String called = reportOf(operation, CALLED, "");
        String written = reportOf(operation, WRITTEN, "");

        assertFalse(pointsOn(called, "q").isEmpty(), called);
        assertEquals(pointsOn(written, "q"), pointsOn(called, "q"), called);
        assertEquals(saidAbout(written, "q"), saidAbout(called, "q"), called);
    }

    /**
     * Where the operation finds something, the default is not what is compared, so a row there at
     * a point of the default's line is at no point of it.
     */
    @ParameterizedTest
    @MethodSource("operationsAnsweringAnOption")
    void theDefaultsLineDecidesOnlyWhereTheOperationFindsNothing(String operation,
                                                                 String presence, String nothing,
                                                                 String something, int found) {
        // A row at each point of the default's line, and one with the other list beside them.
        String rows = """
                example f
                    | "on" : (%1$s, 0) -> %3$s
                    | "off" : (%1$s, 1) -> %4$s
                    | "in" : (%1$s, -3) -> true
                    | "out" : (%1$s, 4) -> %5$s
                    | "beside" : (%2$s, 3) -> %6$s
                """;
        String absent = reportOf(operation, CALLED,
                rows.formatted(nothing, something, true, false, false, found >= 3));
        String present = reportOf(operation, CALLED,
                rows.formatted(something, nothing, found >= 0, found >= 1, found >= 4, false));

        assertEquals(List.of(), unmetPointsOn(absent, "q"), absent);
        // The row beside them finds nothing and is past the line, so the far side is met.
        assertEquals(List.of("· read as f/q: = 0", "· read as f/q: = 1",
                "· read as f/q: in q < 0"), unmetPointsOn(present, "q"), present);
    }

    /** The points on {@code at} no row is at, sorted. */
    private static List<String> unmetPointsOn(String report, String at) {
        List<String> lines = report.lines().map(String::strip).toList();
        List<String> out = new ArrayList<>();
        for (int i = 0; i + 1 < lines.size(); i++) {
            if (lines.get(i).startsWith("! no row is at")
                    && lines.get(i + 1).startsWith("· read as f/" + at + ":")) {
                out.add(lines.get(i + 1));
            }
        }
        return out.stream().sorted().toList();
    }

    /**
     * The statement turns on whether the operation finds something where the default and the value
     * found compare differently with {@code q}, which no row's own values say: that line is said
     * not drawn here, and is drawn where the comparison that states it is written.
     */
    @ParameterizedTest
    @MethodSource("operationsAnsweringAnOption")
    void whetherItFindsSomethingIsNoLineOfTheDefault(String operation, String presence) {
        String called = reportOf(operation, CALLED, "");

        assertEquals(List.of("· not read: comparison — what it states was read, and it is several"
                        + " lines held together, which this compiler does not divide the input by"
                        + " here, about `" + presence + "`"),
                saidAbout(called, presence), called);
        assertEquals(List.of(), saidAbout(called, "xs"), called);
    }

    /**
     * A clause has nowhere to hold where a line decides, so the line on the default is said not
     * drawn; what the value found is related to stays that.
     */
    @Test
    void aClauseKeepsTheValueFoundRelatedBesideTheLinesItCannotHold() {
        Compilation compilation = Compilation.ofSource("""
                module p

                data Ok = { v: Int }

                behavior f : (xs: List<Int>, q: Int) -> Ok
                    constructs Ok
                    ensures found = Option.withDefault(0, List.get(2, xs)) >= q
                let f (xs, q) = Ok { v = q }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertEquals(List.of(
                "· not read: ensures f (found) — what it states was read, and it is several lines"
                        + " held together, which this compiler does not divide the input by here,"
                        + " about `q`",
                "· not read: ensures f (found) — what it states was read, and it relates the value"
                        + " here to another value not shown to reach every value here, so which"
                        + " values here settle it on their own is not worked out, about `q`"),
                saidAbout(report, "q"), report);
    }

    private static String measurement(String report) {
        String line = lineAbout(report, "measurement:");
        return line.substring(line.indexOf("measurement:") + "measurement:".length()).strip();
    }
}
