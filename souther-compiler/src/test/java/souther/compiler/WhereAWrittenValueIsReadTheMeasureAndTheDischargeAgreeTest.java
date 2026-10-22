package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ElementsWrittenOut;
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
 * Where a value is written down, the reading of an input and the discharge of a rule say the same
 * of it: what a {@code Some} arm opens, and how many elements a container holds. Both read the
 * body as {@code c - 48}, or neither does.
 *
 * <p>Each row its own helper and its own two behaviors, asked of both. The measure is read where a guard
 * {@code digitValue(x) >= 5} draws its line, at {@code x = 53} where the body is {@code c - 48};
 * the discharge where {@code Digit(digitValue(c))} under {@code c >= 48} is owed nothing, which it is
 * where the body is {@code c - 48} and is not where nothing says which number is taken from
 * {@code c}.
 */
class WhereAWrittenValueIsReadTheMeasureAndTheDischargeAgreeTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** Each body of {@code digitValue}, and whether it is {@code c - 48} as far as anything says. */
    private static final Map<String, Boolean> ROWS = Map.ofEntries(
            Map.entry(opening("List.get(0, String.codePoints(\"0\"))"), true),
            Map.entry(opening("List.get(1, [7, 48])"), true),
            Map.entry(opening("List.get(0, [fortyEight])"), true),
            Map.entry(opening("List.get(0, List.map(n -> n + 1, [47]))"), true),
            Map.entry(opening("List.get(1, List.flatMap(p -> p, [[7], [48]]))"), true),
            Map.entry(opening("List.get(0, String.codePoints(\""
                    + "0".repeat(ElementsWrittenOut.MOST_WALKED + 1) + "\"))"), true),
            Map.entry(opening("Option.map(n -> n + 1, List.get(0, [47]))"), true),
            Map.entry("c - List.length(String.codePoints(\"" + "0".repeat(48) + "\"))", true),
            Map.entry("c - List.length(List.map(n -> n + 1, String.codePoints(\""
                    + "0".repeat(48) + "\")))", true),
            Map.entry("c - List.length(List.filter(n -> n > 0, [" + "1, ".repeat(47) + "1]))",
                    true),
            Map.entry("c - holding.held", true),
            Map.entry("c - 48 - List.length(List.filter(n -> n > 100,"
                    + " List.filter(n -> n > k, [1, 2])))", true),
            Map.entry(opening("List.get(0, List.map(n -> n, {\n            let zero = 48\n"
                    + "            [zero]\n        }))"), true),
            Map.entry(opening("List.get(0, List.flatMap(p -> p, {\n            let zero = 48\n"
                    + "            [[zero]]\n        }))"), true),
            Map.entry(opening("Option.map(n -> n, List.get(0, {\n            let zero = 48\n"
                    + "            [zero]\n        }))"), true),
            Map.entry(opening("List.get(0, zeros)"), true),
            Map.entry(opening("List.get(0, List.map(n -> n, zeros))"), true),
            Map.entry(opening("Option.map(n -> n, List.get(0, zeros))"), true),
            Map.entry("c - List.length(zeros) - 47", true),
            Map.entry("{\n        let (a, b) = (48, 1)\n        c - a\n    }", true),
            Map.entry("{\n        let r = holding\n        c - r.held\n    }", true),
            Map.entry(opening("List.get(0, xs)"), false),
            Map.entry(opening("List.get(0, List.filter(n -> n > k, [48]))"), false),
            Map.entry(opening("List.get(1, List.flatMap(p -> p, [List.filter(n -> n > k, [7]),"
                    + " [48]]))"), false),
            Map.entry(opening("List.get(" + ElementsWrittenOut.MOST_WALKED
                    + ", String.codePoints(\"" + "0".repeat(ElementsWrittenOut.MOST_WALKED + 1)
                    + "\"))"), false),
            Map.entry(opening("Option.map(n -> n + k, List.get(0, [48]))"), false),
            // As many as 49 of them may be kept, so under `c >= 48` the body may come to one
            // below nought: no reading of how many is taken passes it.
            Map.entry("c - List.length(List.filter(n -> n > k, String.codePoints(\""
                    + "0".repeat(49) + "\")))", false));

    /** A body subtracting what a {@code Some} arm over {@code option} opens. */
    private static String opening(String option) {
        return "match " + option + " with\n"
                + "        | Some zero -> c - zero\n"
                + "        | None -> 0";
    }

    /** {@code bodies}, each a {@code digitValue} with the two behaviors that read it beside it. */
    private static String program(List<String> bodies) {
        StringBuilder each = new StringBuilder();
        for (int at = 0; at < bodies.size(); at++) {
            each.append("""

                    let digitValue%1$d (c: Int, xs: List<Int>, k: Int): Int =
                        %2$s

                    behavior check%1$d : (x: Int, xs: List<Int>, k: Int) -> Int | Bad
                    let check%1$d (x, xs, k) = {
                        guard digitValue%1$d(x, xs, k) >= 5 else Bad
                        0
                    }

                    behavior f%1$d : (c: Int, xs: List<Int>, k: Int) -> Digit
                        constructs Digit
                    let f%1$d (c, xs, k) =
                        if c >= 48 then Digit(digitValue%1$d(c, xs, k)) else Digit(0)
                    """.formatted(at, bodies.get(at)));
        }
        return """
                module demo

                data Bad
                data Digit = Int
                    invariant atLeastNought = value >= 0

                let fortyEight = 48

                data Holder = { held: Int }
                let holding = Holder { held = 48 }

                let zeros: List<Int> = {
                    let zero = 48
                    [zero]
                }
                %s""".formatted(each);
    }

    /**
     * The bodies that are {@code c - 48} are one module, each with its own two behaviors: each
     * {@code check} is measured on its own lines, and the discharge owes nothing anywhere. A body
     * that is not is a module of its own, so the warning it is owed is its own.
     */
    @Test
    void eachProgramIsReadAlikeByBoth() {
        List<String> disagreeing = new ArrayList<>();
        List<String> fortyEight = ROWS.entrySet().stream().filter(Map.Entry::getValue)
                .map(Map.Entry::getKey).toList();
        Compilation together = measured(program(fortyEight));
        JsonNode report = reportOf(together);
        for (int at = 0; at < fortyEight.size(); at++) {
            Set<String> points = pointsOn(report, "check" + at + "/x");
            if (!points.equals(Set.of("52", "53"))) {
                disagreeing.add(fortyEight.get(at) + ": measured " + points + ", expected true");
            }
        }
        List<Located> owed = owed(together);
        if (!owed.isEmpty()) {
            disagreeing.add("discharged none of " + owed.stream()
                    .map(each -> each.diagnostic().said()).toList() + ", expected all");
        }
        ROWS.forEach((body, isFortyEight) -> {
            if (isFortyEight) {
                return;
            }
            Compilation compilation = measured(program(List.of(body)));
            Set<String> points = pointsOn(reportOf(compilation), "check0/x");
            boolean measured = points.equals(Set.of("52", "53"));
            boolean discharged = owed(compilation).isEmpty();
            if (measured || discharged) {
                disagreeing.add(body + ": measured " + points + ", discharged " + discharged
                        + ", expected false");
            }
        });
        assertEquals(List.of(), disagreeing, "each row is read as its expectation by both");
    }

    /** What the discharge left owed: its warnings. */
    private static List<Located> owed(Compilation compilation) {
        return compilation.warnings().stream()
                .filter(each -> each.diagnostic().severity() == Severity.WARNING
                        && "E2011".equals(each.diagnostic().code()))
                .toList();
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
