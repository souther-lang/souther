package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.diag.Severity;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a law of the library says something of a call, the reading of an input and the discharge of
 * a rule both take it: which arm of a match on what the call answered is taken, how many a
 * container it answered holds, whether it holds anything, and what number it answers in each of
 * the cases the library defines it in.
 *
 * <p>One program per row, asked of both, and each side held to its own expectation rather than to
 * the other's: two readings agreeing on a wrong answer is not what is asked. The measure is read
 * where a guard {@code helper(x) >= 5} draws its lines; the discharge where
 * {@code Digit(helper(c))} under {@code c >= from} is owed nothing. Each law is asked once where it
 * settles the body and once where it leaves a value the invariant refuses, so neither side can pass
 * by refusing, or by proving, everything.
 */
class WhereALibraryLawIsReadTheMeasureAndTheDischargeAgreeTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * A body of {@code helper}, read under {@code c >= from}: the values at and beside the lines the
     * measure draws on {@code check}'s input, and whether the discharge owes nothing.
     */
    private record Row(String body, int from, Set<String> measured, boolean discharged) {}

    private static final List<Row> ROWS = List.of(
            // The absent arm of a maximum of a list holding something is never taken.
            new Row("match List.max([c, 7]) with\n        | Some m -> c\n        | None -> 0 - 1",
                    0, Set.of("4", "5"), true),
            new Row("match List.max(List.filter(n -> n > 100, [c])) with\n"
                    + "        | Some m -> c\n        | None -> 0 - 1",
                    0, Set.of("100", "101"), false),
            // A list put together of two holds as many as both.
            new Row("c + 3 - List.length(List.append([c], [c, c]))", 0, Set.of("4", "5"), true),
            new Row("c + 3 - List.length(List.append([c], [c, c, c]))", 0, Set.of("5", "6"),
                    false),
            // A filter keeping an element written out on every run holds something; the line of
            // the step's own comparison is drawn as any written comparison's is.
            new Row("if List.isEmpty(List.filter(n -> n > 2, [c, 3])) then 0 - 1 else c", 0,
                    Set.of("2", "3", "4", "5"), true),
            new Row("if List.isEmpty(List.filter(n -> n > 2, [c])) then 0 - 1 else c", 0,
                    Set.of("2", "3", "4", "5"), false),
            // And through the name it was given.
            new Row("{\n        let kept = [c, 3]\n"
                    + "        if List.isEmpty(List.filter(n -> n > 2, kept)) then 0 - 1 else c\n"
                    + "    }", 0, Set.of("2", "3", "4", "5"), true),
            // And none where every element written out fails the step on every run.
            new Row("if List.isEmpty(List.filter(n -> n > 5, [1, 3])) then c else 0 - 1", 0,
                    Set.of("4", "5"), true),
            // A list taken from holds as many as its case says, whichever the case turns on: the
            // number asked for against how many there are, written down or not.
            new Row("c + 2 - List.length(List.take(2, [1, 2, 3]))", 0, Set.of("4", "5"), true),
            new Row("c + 1 - List.length(List.take(2, [1, 2, 3]))", 0, Set.of("5", "6"), false),
            new Row("c - List.length(List.take(c, [1, 2, 3]))", 0, Set.of("7", "8"), true),
            new Row("c - 1 - List.length(List.take(c, [1, 2, 3]))", 0, Set.of("8", "9"), false),
            // A size read from one expression in two environments is two sizes.
            new Row("c + 5 - grown([c]) - grown([c, c])", 0, Set.of("4", "5"), true),
            new Row("c + 4 - grown([c]) - grown([c, c])", 0, Set.of("5", "6"), false),
            // A comparison answers one of three numbers by how the two stand.
            new Row("c + 1 + Int.compare(c, 0)", 0, Set.of("2", "3"), true),
            new Row("Int.compare(c, 0) + 4", 0, Set.of("0", "1"), true),
            new Row("c - 1 + Int.compare(c, 0)", 0, Set.of("4", "5"), false),
            // A magnitude of a number written down is the number its case answers.
            new Row("c - Int.abs(0 - 48)", 48, Set.of("52", "53"), true),
            new Row("c - Int.abs(0 - 49)", 48, Set.of("53", "54"), false),
            // And of a number not written down, case by case and not only by where it lies: the
            // magnitude of a number at or above nought is that number.
            new Row("c - Int.abs(c)", 0, Set.of(), true),
            new Row("c - Int.abs(c - 2)", 0, Set.of(), false));

    private static String program(Row row) {
        return """
                module demo

                data Bad
                data Digit = Int
                    invariant atLeastNought = value >= 0

                let grown (xs: List<Int>): Int = List.length(List.append(xs, [7]))

                let helper (c: Int): Int =
                    %s

                behavior check : (x: Int) -> Int | Bad
                let check (x) = {
                    guard helper(x) >= 5 else Bad
                    0
                }

                behavior f : (c: Int) -> Digit
                    constructs Digit
                let f (c) =
                    if c >= %d then Digit(helper(c)) else Digit(0)
                """.formatted(row.body(), row.from());
    }

    @Test
    void eachProgramIsReadAsItsLawSaysByBoth() {
        List<String> disagreeing = new ArrayList<>();
        for (Row row : ROWS) {
            Compilation compilation = measured(program(row));
            Set<String> points = pointsOn(reportOf(compilation), "check/x");
            boolean discharged = compilation.warnings().stream().map(Located::diagnostic)
                    .noneMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
            if (!points.equals(row.measured()) || discharged != row.discharged()) {
                disagreeing.add(row.body() + ": measured " + points + ", discharged " + discharged
                        + ", expected " + new TreeSet<>(row.measured()) + " and "
                        + row.discharged());
            }
        }
        assertEquals(List.of(), disagreeing, "each row is read as its law says by both");
    }

    /** Every value at or beside a line of the statement a row is owed at, on {@code axis}. */
    private static Set<String> pointsOn(JsonNode report, String axis) {
        Set<String> out = new TreeSet<>();
        collect(report, axis, out);
        return out;
    }

    private static void collect(JsonNode node, String axis, Set<String> out) {
        if (node.isObject() && node.has("point") && node.has("readings")
                && Set.of("at_the_line", "beside_the_line").contains(
                        node.at("/obligationId/location/kind").asString())) {
            JsonNode reading = node.path("readings").get(0);
            if (reading.path("axis").asString().equals(axis)) {
                out.add(reading.path("against").asString());
            }
        }
        node.forEach(child -> collect(child, axis, out));
    }

    /** {@code model} compiled once, its rules discharged and its examples measured. */
    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "compiles: " + compilation.errors()
                .stream().map(e -> e.diagnostic().code()).toList() + "\n" + model);
        return compilation;
    }

    private static JsonNode reportOf(Compilation compilation) {
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }
}
