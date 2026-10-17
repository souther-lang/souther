package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two names for two elements of one container are two values, and a comparison of them is not read
 * as a comparison of one position with itself.
 *
 * <p>A position inside a container's elements says an element and not which one, so two such names
 * are one position and a form over both holds one number twice: {@code a - b} over two entries of
 * one map is {@code m[*] - m[*]}, which cancels. Read to the end, that is a rule that cuts nothing
 * — said of a comparison that cuts a good deal — and a decision rule taken where it holds is proved
 * never to be taken. What is read of one element of each container is read; a comparison of two is
 * said to be one this does not read, and the measurement is partial.
 */
class TwoEntriesOfOneContainerAreNotReadAsOneTest {

    private static final String TWO_LOOKUPS = """
            module p
            behavior f : (m: Map<String, Int>) -> Bool
            let f (m) =
                match Map.get("A", m) with
                    | Some a ->
                        match Map.get("B", m) with
                            | Some b -> a > b
                            | None -> false
                    | None -> false
            """;

    private static final String TWO_ELEMENTS = """
            module p
            behavior f : (xs: List<Int>) -> Bool
            let f (xs) = List.any(x -> List.any(y -> x > y, xs), xs)
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

    private static List<String> errors(Compilation compilation) {
        return compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList();
    }

    /** What the definition answers, whatever the analysis makes of it. */
    @Test
    void twoLookupsOfOneMapAnswerAsTheDefinitionSays() {
        Compilation compilation = measured(TWO_LOOKUPS + """

                example f
                    | "A above B" : ([("A", 2), ("B", 1)]) -> true
                    | "A below B" : ([("A", 1), ("B", 2)]) -> false
                    | "A equal to B" : ([("A", 2), ("B", 2)]) -> false
                    | "B absent" : ([("A", 1)]) -> false
                    | "A absent" : ([("B", 1)]) -> false
                    | "neither" : ([]) -> false
                """);

        assertEquals(List.of(), errors(compilation), () -> report(compilation));
    }

    /**
     * And the analysis does not read the comparison of the two as one that cuts nothing, nor take
     * the arm it is in as one no row reaches: it says the comparison names two elements of one map,
     * and the measurement is partial.
     */
    @Test
    void theComparisonOfTwoEntriesIsSaidToBeOneThisDoesNotRead() {
        String report = report(measured(TWO_LOOKUPS));

        assertFalse(report.contains("cuts nothing"), report);
        assertTrue(report.contains("two elements of one"), report);
        assertTrue(report.contains("measurement: partial"), report);
    }

    /**
     * The same defect where it was met first, with nothing of a lookup in it: two names for two
     * elements of one list, one inside the other.
     */
    @Test
    void twoElementsOfOneListAreNotOnePositionEither() {
        String report = report(measured(TWO_ELEMENTS));

        assertFalse(report.contains("cuts nothing"), report);
        assertTrue(report.contains("two elements of one"), report);
    }

    /**
     * What is read of one element of each container is still read: the same two lookups with a
     * comparison that names only one of the entries.
     */
    @Test
    void aComparisonOfOneEntryBesideAnotherLookupIsStillRead() {
        String report = report(measured("""
                module p
                behavior f : (k1: String, k2: String, m: Map<String, Int>) -> Bool
                let f (k1, k2, m) =
                    match Map.get(k1, m) with
                        | Some a ->
                            match Map.get(k2, m) with
                                | Some b -> a > 0
                                | None -> false
                        | None -> false
                """));

        assertFalse(report.contains("two elements of one"), report);
        assertTrue(report.contains("read as f/m[*]"), report);
    }

    /**
     * An entry an arm picked out, added to another entry of the same map taken with a default, is
     * two entries in one comparison however the second was taken out, and is not read as twice one
     * entry. The same comparison with the second entry from another map is read.
     */
    @Test
    void anEntryAnArmPickedOutBesideAnotherTakenWithADefaultIsNotReadAsOne() {
        String model = """
                module p
                behavior f : (k: String, j: String, m: Map<String, Int>, n: Map<String, Int>,
                              q: Int) -> Bool
                let f (k, j, m, n, q) =
                    match Map.get(k, m) with
                        | Some a -> a + Option.withDefault(0, Map.get(j, %s)) >= q
                        | None -> false
                """;
        String oneMap = report(measured(model.formatted("m")));
        assertFalse(oneMap.contains("2 * m[*]"), oneMap);
        assertTrue(oneMap.contains("does not read, about `m[*]`"), oneMap);

        String twoMaps = report(measured(model.formatted("n")));
        assertFalse(twoMaps.contains("two elements of one"), twoMaps);
        assertTrue(twoMaps.contains("read as f/m[*] + n[*] - q"), twoMaps);
    }

    private static final Pattern ENTRY = Pattern.compile("\\(\"([^\"]*)\", (-?\\d+)\\)");

    /**
     * The rows offered for the comparison of one entry hold the entry under the first key at the
     * line and say nothing of the other's value: each is answered by the definition and run.
     */
    @Test
    void theRowsOfferedForOneEntryAreAnsweredByTheDefinition() {
        String model = """
                module p
                behavior f : (k1: String, k2: String, m: Map<String, Int>) -> Bool
                let f (k1, k2, m) =
                    match Map.get(k1, m) with
                        | Some a ->
                            match Map.get(k2, m) with
                                | Some b -> a > 0
                                | None -> false
                        | None -> false
                """;
        Compilation compilation = measured(model);
        Generator.GenerationResult offered =
                OfferedAtTheLines.of(compilation, compilation.modules().get(0), "f");
        assertFalse(offered.rows().isEmpty(), "rows are offered for the line");

        StringBuilder examples = new StringBuilder("\nexample f\n");
        int number = 0;
        for (Generator.GeneratedRow row : offered.rows()) {
            List<FixtureTemplate> inputs = row.inputs();
            Map<String, Long> entries = new LinkedHashMap<>();
            Matcher entry = ENTRY.matcher(inputs.get(2).text());
            while (entry.find()) {
                entries.put(entry.group(1), Long.parseLong(entry.group(2)));
            }
            String first = inputs.get(0).text().replace("\"", "");
            String second = inputs.get(1).text().replace("\"", "");
            boolean answer = entries.containsKey(first) && entries.containsKey(second)
                    && entries.get(first) > 0;
            examples.append("    | \"row ").append(++number).append("\" : (")
                    .append(String.join(", ", inputs.stream().map(FixtureTemplate::text).toList()))
                    .append(") -> ").append(answer).append('\n');
        }

        assertEquals(List.of(), errors(measured(model + examples)),
                () -> examples + report(measured(model + examples)));
    }
}
