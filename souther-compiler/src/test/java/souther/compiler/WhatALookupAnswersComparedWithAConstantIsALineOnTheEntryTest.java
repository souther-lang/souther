package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a lookup answers, with a default where nothing is filed under the key, compared as a whole
 * with a constant: some entry under the key whose value meets the comparison. The line is the
 * comparison's on that entry, where the same comparison written under the arm draws it.
 *
 * <p>A default the constant puts on the other side is no way the comparison holds, so what is
 * stated is the entry alone — no either-or with the default — and it is read all the same.
 */
class WhatALookupAnswersComparedWithAConstantIsALineOnTheEntryTest {

    private static final String AS_A_WHOLE = """
            module p
            behavior f : (k: String, m: Map<String, Int>) -> Bool
            let f (k, m) = (match Map.get(k, m) with
                    | Some v -> v
                    | None -> 0) >= 1
            """;

    private static final String UNDER_THE_ARM = """
            module p
            behavior f : (k: String, m: Map<String, Int>) -> Bool
            let f (k, m) =
                match Map.get(k, m) with
                    | Some v -> v >= 1
                    | None -> false
            """;

    private static final String THROUGH_THE_DEFAULT = """
            module p
            behavior f : (k: String, m: Map<String, Int>) -> Bool
            let f (k, m) = (Map.get(k, m) |> Option.withDefault(0)) >= 1
            """;

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> linesRead(String report) {
        return report.lines().filter(line -> line.contains("read as")).map(String::strip)
                .sorted().toList();
    }

    @Test
    void itDrawsTheLineTheComparisonUnderTheArmDraws() {
        String written = report(measured(UNDER_THE_ARM));
        for (String model : List.of(AS_A_WHOLE, THROUGH_THE_DEFAULT)) {
            String report = report(measured(model));

            assertFalse(report.contains("not read"), report);
            assertTrue(report.contains("measurement: complete"), report);
            assertEquals(linesRead(written), linesRead(report), report);
        }
    }

    /** Every row offered for a line files a value under the key, at the line. */
    @Test
    void aRowOfferedForTheLineFilesTheValueUnderTheKey() {
        List<Row> rows = offered(AS_A_WHOLE);

        assertEquals(4, rows.size(), rows::toString);
        for (Row row : rows) {
            assertTrue(row.entries().containsKey(row.key()), row::toString);
            long value = row.entries().get(row.key());
            switch (row.label()) {
                case "m[*] = 1" -> assertEquals(1, value, row::toString);
                case "m[*] = 0" -> assertEquals(0, value, row::toString);
                case "1 < m[*]" -> assertTrue(1 < value, row::toString);
                case "m[*] < 0" -> assertTrue(value < 0, row::toString);
                default -> throw new AssertionError("a line nobody expected: " + row);
            }
        }
    }

    /** The rows offered, answered as the lookup is defined, are all the model asks. */
    @Test
    void theRowsOfferedAreAnsweredByTheDefinitionAndSatisfyTheModel() {
        StringBuilder examples = new StringBuilder("\nexample f\n");
        for (Row row : offered(AS_A_WHOLE)) {
            examples.append("    | \"").append(row.label()).append("\" : (")
                    .append(String.join(", ", row.inputTexts())).append(") -> ")
                    .append(row.entries().getOrDefault(row.key(), 0L) >= 1).append('\n');
        }
        Compilation answered = measured(AS_A_WHOLE + examples + """
                    | "nothing under the key" : ("x", []) -> false
                """);

        assertEquals(List.of(), answered.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                () -> examples + report(answered));
        assertTrue(report(answered).contains("adequacy: satisfied"), () -> report(answered));
    }

    /** Another key holding the value at a point puts no row there. */
    @Test
    void anotherKeyHoldingTheValueAtAPointPutsNoRowThere() {
        assertFalse(undecidedAfter("(\"A\", [(\"A\", 1)]) -> true").contains("ON"));
        assertTrue(undecidedAfter("(\"A\", [(\"B\", 1), (\"A\", 5)]) -> true").contains("ON"));
    }

    private static List<String> undecidedAfter(String row) {
        String report = report(measured(AS_A_WHOLE + """

                example f
                    | "one row" : %s
                """.formatted(row)));
        List<String> lines = report.lines().toList();
        List<String> out = new ArrayList<>();
        for (int i = 0; i + 1 < lines.size(); i++) {
            Matcher point = Pattern.compile("no row is at (?:the|an) (\\w+) point")
                    .matcher(lines.get(i));
            if (point.find() && lines.get(i + 1).contains("read as f/m[*]")) {
                out.add(point.group(1));
            }
        }
        return out;
    }

    /** One row offered for a line: what it was offered for, and the values it writes. */
    private record Row(String label, List<String> inputTexts, String key,
                       Map<String, Long> entries) {}

    private static final Pattern ENTRY = Pattern.compile("\\(\"([^\"]*)\", (-?\\d+)\\)");

    private static List<Row> offered(String model) {
        Compilation compilation = measured(model);
        Generator.GenerationResult result =
                OfferedAtTheLines.of(compilation, compilation.modules().get(0), "f");
        List<Row> out = new ArrayList<>();
        for (Generator.GeneratedRow row : result.rows()) {
            List<String> texts = row.inputs().stream().map(FixtureTemplate::text).toList();
            Map<String, Long> entries = new LinkedHashMap<>();
            Matcher entry = ENTRY.matcher(texts.get(1));
            while (entry.find()) {
                entries.put(entry.group(1), Long.parseLong(entry.group(2)));
            }
            String key = texts.get(0).substring(1, texts.get(0).length() - 1);
            String label = row.purposes().stream()
                    .filter(Generator.Purpose.ForAPoint.class::isInstance)
                    .map(each -> ((Generator.Purpose.ForAPoint) each).label())
                    .findFirst().orElseThrow();
            out.add(new Row(label, texts, key, entries));
        }
        assertEquals(List.of(), result.unresolved(), "every point is offered a row");
        return out;
    }
}
