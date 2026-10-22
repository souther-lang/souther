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
 * What a lookup in a map of the input answers is the value of the entry whose key is the one asked
 * for, and a condition on it is read of that entry and not of another.
 *
 * <p>Said as the statement it is: some entry filed under the key, and of that entry the value meets
 * what the arm asks. A key and a value read of two different entries would be a row that stands at
 * a line of one entry while the lookup answers the other, so a row offered for a line of the value
 * is one whose entry under the key is the one at the line.
 */
class AMapLookupIsReadAsTheEntryItSelectsTest {

    private static final String WITH_DEFAULT = """
            module p
            behavior f : (k: String, m: Map<String, Int>, q: Int) -> Bool
            let f (k, m, q) = (Map.get(k, m) |> Option.withDefault(0)) >= q
            """;

    private static final String WRITTEN_OUT = """
            module p
            behavior f : (k: String, m: Map<String, Int>, q: Int) -> Bool
            let f (k, m, q) =
                match Map.get(k, m) with
                    | Some v -> v >= q
                    | None -> 0 >= q
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

    private static String lineAbout(String report, String word) {
        return report.lines().filter(line -> line.contains(word)).findFirst().orElse("");
    }

    /** What the model says, as the lookup is defined: the default stands where nothing is filed. */
    private static boolean answer(String key, Map<String, Long> entries, long q) {
        return entries.getOrDefault(key, 0L) >= q;
    }

    /**
     * Nothing is left unread, the threshold included. On the way to the entry the lookup asks
     * which key the map holds an entry under, which says nothing of the value under it, so the
     * entry's value reaches every threshold — written with the default or with the match spelled
     * out, and with the value moved by a constant before it is compared.
     */
    @Test
    void aLookupWithADefaultIsReadToTheEnd() {
        for (String source : List.of(WITH_DEFAULT, WRITTEN_OUT, """
                module p
                behavior f : (k: String, m: Map<String, Int>, q: Int) -> Bool
                let f (k, m, q) =
                    (Map.get(k, m) |> Option.map(v -> v + 1) |> Option.withDefault(0)) >= q
                """)) {
            String report = report(measured(source));

            assertEquals(List.of(), notRead(report), report);
        }
    }

    /**
     * A condition on the value under the key still holds it back: past the entry's value at ten
     * or more, a threshold of ten or below is met by every entry, and is not reached.
     */
    @Test
    void aConditionOnTheEntrysValueStillHoldsItBack() {
        String report = report(measured("""
                module p
                behavior f : (k: String, m: Map<String, Int>, q: Int) -> Bool
                let f (k, m, q) = (Map.get(k, m) |> Option.withDefault(0)) >= 10
                    && (Map.get(k, m) |> Option.withDefault(0)) >= q
                """));

        assertEquals(1, notRead(report).size(), report);
        assertTrue(notRead(report).getFirst().contains("not shown to reach every value here")
                && notRead(report).getFirst().endsWith("about `q`"), report);
    }

    /** The lines {@code report} says were not read. */
    private static List<String> notRead(String report) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith("· not read")).toList();
    }

    /**
     * The entry's line decides wherever an entry is filed under the key, whatever the default is
     * against the threshold: where none is, the entry's comparison is not what the statement
     * says. Read so, the threshold runs over every value on the way to the entry, and what the
     * entry's value is said to be is what the match written out says of it.
     */
    @Test
    void theDefaultsLineDoesNotDivideWhereTheEntrysLineDecides() {
        String called = report(measured(WITH_DEFAULT));
        String written = report(measured(WRITTEN_OUT));

        assertEquals(partitionAbout(written, "m[*]"), partitionAbout(called, "m[*]"), called);
        assertTrue(partitionAbout(called, "m[*]").startsWith("· no line:"), called);
    }

    /** The partition line about {@code place}, without where its comparison stands. */
    private static String partitionAbout(String report, String place) {
        return report.lines().map(String::strip)
                .filter(line -> line.endsWith("about `" + place + "`"))
                .map(line -> line.replaceFirst("comparison@\\d+:\\d+", "comparison"))
                .findFirst().orElse("");
    }

    /**
     * The default stands where the key is not filed, so its side of the statement is the default
     * against the threshold: no entry, and {@code 0 >= q}.
     */
    @Test
    void itDrawsTheLinesTheMatchWithTheDefaultWrittenOutDraws() {
        String called = report(measured(WITH_DEFAULT));
        String written = report(measured(WRITTEN_OUT));

        assertEquals(lineAbout(written, "border "), lineAbout(called, "border "), called);
        assertTrue(lineAbout(called, "border ").contains("borders 2"), called);
        assertTrue(called.contains("read as f/q: = 1"), called);
        assertTrue(called.contains("read as f/q: = 0"), called);
        assertTrue(called.contains("read as f/m[*]: = q"), called);
    }

    /**
     * Every row offered for a line of the entry's value has an entry under the key, and the value
     * of that entry is where the line puts it; every row offered for the line of the default has
     * none.
     */
    @Test
    void aRowOfferedForTheEntrysValueIsOneWhoseEntryUnderTheKeyIsAtTheLine() {
        List<Row> rows = offered(WITH_DEFAULT);

        assertEquals(8, rows.size(), rows::toString);
        for (Row row : rows) {
            if (row.label().contains("m[*]")) {
                assertTrue(row.entries().containsKey(row.key()),
                        () -> "an entry is filed under the key: " + row);
                long value = row.entries().get(row.key());
                switch (row.label()) {
                    case "m[*] = q" -> assertEquals(row.q(), value, row::toString);
                    case "m[*] = q - 1" -> assertEquals(row.q() - 1, value, row::toString);
                    case "q < m[*]" -> assertTrue(row.q() < value, row::toString);
                    case "m[*] < q - 1" -> assertTrue(value < row.q() - 1, row::toString);
                    default -> throw new AssertionError("a line nobody expected: " + row);
                }
            } else {
                assertFalse(row.entries().containsKey(row.key()),
                        () -> "the default stands where nothing is filed under the key: " + row);
            }
        }
    }

    /**
     * The rows offered, answered by what the lookup is defined to answer and put back as examples,
     * are all the model asks: they run, and each answers the line it was offered for.
     */
    @Test
    void theRowsOfferedAreAnsweredByTheDefinitionAndSatisfyTheModel() {
        Compilation offered = measured(WITH_DEFAULT);
        StringBuilder examples = new StringBuilder("\nexample f\n");
        for (Row row : offered(WITH_DEFAULT)) {
            examples.append("    | \"").append(row.label()).append("\" : (")
                    .append(String.join(", ", row.inputTexts())).append(") -> ")
                    .append(answer(row.key(), row.entries(), row.q())).append('\n');
        }
        Compilation answered = measured(WITH_DEFAULT + examples);

        assertEquals(List.of(), answered.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                () -> examples + report(answered));
        assertFalse(report(answered).contains("adequacy: not satisfied"),
                () -> report(answered));
        assertEquals(List.of(), notRead(report(answered)), () -> report(answered));
        assertEquals(8, offered(WITH_DEFAULT).size(), () -> report(offered));
    }

    /** The value read is the one filed under the key, whatever else the map holds. */
    @Test
    void aValueUnderAnotherKeyIsNotTheOneTheLookupAnswers() {
        for (String model : List.of(WITH_DEFAULT, WRITTEN_OUT)) {
            Compilation compilation = measured(model + """

                    example f
                        | "present, at the line" : ("A", [("A", 5)], 5) -> true
                        | "present, under it" : ("A", [("A", 4)], 5) -> false
                        | "absent, threshold above the default" : ("A", [], 1) -> false
                        | "absent, threshold below the default" : ("A", [], -1) -> true
                        | "another key holds the large value" : ("A", [("B", 10), ("A", 2)], 5) -> false
                        | "another key holds the small value" : ("A", [("B", 1), ("A", 9)], 5) -> true
                        | "only another key is filed" : ("A", [("B", 99)], 1) -> false
                    """);

            assertEquals(List.of(), compilation.errors().stream()
                    .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                    .toList(), () -> model);
        }
    }

    /** The control: the same rows with one answer the lookup does not give are refused. */
    @Test
    void anAnswerTheLookupDoesNotGiveIsRefused() {
        Compilation compilation = measured(WITH_DEFAULT + """

                example f
                    | "another key holds the large value" : ("A", [("B", 10), ("A", 2)], 5) -> true
                """);

        assertFalse(compilation.errors().isEmpty(), () -> report(compilation));
    }

    /** One row offered for a line: what it was offered for, and the values it writes. */
    private record Row(String label, List<String> inputTexts, String key,
                       Map<String, Long> entries, long q) {}

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
            out.add(new Row(label, texts, key, entries, Long.parseLong(texts.get(2))));
        }
        assertEquals(List.of(), result.unresolved(), "every point is offered a row");
        return out;
    }
}
