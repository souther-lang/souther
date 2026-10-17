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
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a {@code Some} arm opens {@code List.get(i, xs)}, the reading of the input and the discharge
 * of a rule say the same of which element it is: both read {@code c - zero} as {@code c - 48}, or
 * neither does.
 *
 * <p>One program per row, asked of both. The measure is read where a guard
 * {@code digitValue(x) >= 5} draws its line, at {@code x = 53} where the element is forty-eight;
 * the discharge where {@code Digit(digitValue(c))} under {@code c >= 48} is owed nothing, which it is
 * where the element is forty-eight and is not where nothing says which number the element is.
 */
class WhereAnElementIsPickedTheMeasureAndTheDischargeAgreeTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** Each scrutinee, and whether the element it holds is forty-eight as far as anything says. */
    private static final Map<String, Boolean> ROWS = Map.ofEntries(
            Map.entry("List.get(0, String.codePoints(\"0\"))", true),
            Map.entry("List.get(1, [7, 48])", true),
            Map.entry("List.get(0, [fortyEight])", true),
            Map.entry("List.get(0, List.map(n -> n + 1, [47]))", true),
            Map.entry("List.get(1, List.flatMap(p -> p, [[7], [48]]))", true),
            Map.entry("List.get(0, String.codePoints(\"" + "0".repeat(2000) + "\"))", true),
            Map.entry("List.get(0, xs)", false),
            Map.entry("List.get(0, List.filter(n -> n > k, [48]))", false),
            Map.entry("List.get(1, List.flatMap(p -> p, [List.filter(n -> n > k, [7]), [48]]))",
                    false),
            Map.entry("List.get(1024, String.codePoints(\"" + "0".repeat(1025) + "\"))", false));

    private static String program(String picked) {
        return """
                module demo

                data Bad
                data Digit = Int
                    invariant atLeastNought = value >= 0

                let fortyEight = 48

                let digitValue (c: Int, xs: List<Int>, k: Int): Int =
                    match %s with
                        | Some zero -> c - zero
                        | None -> 0

                behavior check : (x: Int, xs: List<Int>, k: Int) -> Int | Bad
                let check (x, xs, k) = {
                    guard digitValue(x, xs, k) >= 5 else Bad
                    0
                }

                behavior f : (c: Int, xs: List<Int>, k: Int) -> Digit
                    constructs Digit
                let f (c, xs, k) =
                    if c >= 48 then Digit(digitValue(c, xs, k)) else Digit(0)
                """.formatted(picked);
    }

    @Test
    void eachProgramIsReadAlikeByBoth() {
        List<String> disagreeing = new ArrayList<>();
        ROWS.forEach((picked, fortyEight) -> {
            Compilation compilation = measured(program(picked));
            boolean measured = pointsOn(reportOf(compilation), "check/x")
                    .equals(Set.of("52", "53"));
            boolean discharged = compilation.warnings().stream().map(Located::diagnostic)
                    .noneMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
            if (measured != fortyEight || discharged != fortyEight) {
                disagreeing.add(picked + ": measured " + measured + ", discharged " + discharged
                        + ", expected " + fortyEight);
            }
        });
        assertEquals(List.of(), disagreeing, "each row is read as its expectation by both");
    }

    /** Every value at or beside a line of the statement a row is owed at, on {@code axis}. */
    private static Set<String> pointsOn(JsonNode report, String axis) {
        Set<String> out = new TreeSet<>();
        collect(report, axis, out);
        return out;
    }

    private static void collect(JsonNode node, String axis, Set<String> out) {
        if (node.isObject() && node.has("point") && node.has("readings")
                && "part_of_comparison".equals(
                        node.at("/obligationId/line/which/kind").asString())
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
                .stream().map(e -> e.diagnostic().code()).toList());
        return compilation;
    }

    private static JsonNode reportOf(Compilation compilation) {
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }
}
