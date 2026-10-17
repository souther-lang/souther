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
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an option {@code Option.map} answers holds is what its closure made of the value the option
 * it was handed holds, and a name an arm binds to it, or the closure's own parameter, is read as
 * that.
 *
 * <p>Two things and not one: the value is what the closure made, and the entry of a map it was
 * made of is which entry the statement is about. {@code Option.map(x -> x + 1, Map.get(k, m))}
 * holds the entry's value and one more, so the line is a line of the entry one below the
 * threshold; and a row offered for it files the value under the key the lookup asks for, whatever
 * else the map holds.
 */
class WhatAnOptionMadeByAClosureHoldsIsWhatTheClosureMadeTest {

    private static final String RECORD = """
            module p
            data RoleNode = { holder: String }
            """;

    /** The issue's own: a list of one made of the entry, or none. */
    private static final String OWN = RECORD + """
            behavior f : (node: RoleNode, byOwner: Map<String, Int>) -> Bool
            let own (node: RoleNode, byOwner: Map<String, Int>): List<Int> =
                Map.get(node.holder, byOwner) |> Option.map(one -> [ one ]) |> Option.withDefault([])
            let f (node, byOwner) = Bool.not(List.isEmpty(own(node, byOwner)))
            """;

    private static final String MATCHED = """
            module p
            behavior f : (k: String, m: Map<String, Int>) -> Bool
            let f (k, m) =
                match Option.map(one -> [ one ], Map.get(k, m)) with
                    | Some values -> Bool.not(List.isEmpty(values))
                    | None -> false
            """;

    private static final String ONE_MORE = """
            module p
            behavior f : (k: String, m: Map<String, Int>, q: Int) -> Bool
            let f (k, m, q) = (Map.get(k, m) |> Option.map(v -> v + 1) |> Option.withDefault(0)) >= q
            """;

    /** The same written out: the name under the arm is the entry, and one is added to it there. */
    private static final String ONE_MORE_WRITTEN_OUT = """
            module p
            behavior f : (k: String, m: Map<String, Int>, q: Int) -> Bool
            let f (k, m, q) =
                match Map.get(k, m) with
                    | Some v -> v + 1 >= q
                    | None -> 0 >= q
            """;

    private static final String CONSTANT = """
            module p
            behavior f : (k: String, m: Map<String, Int>, q: Int) -> Bool
            let f (k, m, q) = (Map.get(k, m) |> Option.map(v -> 42) |> Option.withDefault(0)) >= q
            """;

    private static final String TWICE = """
            module p
            behavior f : (k: String, m: Map<String, Int>, q: Int) -> Bool
            let f (k, m, q) = (Map.get(k, m) |> Option.map(v -> v * 2) |> Option.map(w -> w + 1)
                |> Option.withDefault(0)) >= q
            """;

    private static final String AT_A_POSITION = """
            module p
            data H = { qty: Option<Int>, q: Int }
            behavior f : (h: H) -> Bool
            let f (h) = (h.qty |> Option.map(v -> v + 1) |> Option.withDefault(0)) >= h.q
            """;

    private static final String INSIDE_THE_CLOSURE = """
            module p
            behavior f : (k: String, m: Map<String, Int>) -> Bool
            let f (k, m) = (Map.get(k, m) |> Option.map((v) -> if v > 0 then 1 else 0)
                |> Option.withDefault(0)) >= 1
            """;

    private static final String INSIDE_THE_ARM = """
            module p
            behavior f : (k: String, m: Map<String, Int>) -> Bool
            let f (k, m) = (match Map.get(k, m) with
                    | Some v -> if v > 0 then 1 else 0
                    | None -> 0) >= 1
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

    private static String report(String source) {
        return report(measured(source));
    }

    private static List<String> linesAbout(String report, String word) {
        return report.lines().filter(line -> line.contains(word)).map(String::strip).sorted()
                .toList();
    }

    /**
     * Whether everything {@code report} says went unread is that a relation is not shown to reach
     * every value of a place: a threshold the input holds is related to what the closure made,
     * and where what it was made of is a lookup's entry, the lookup's condition on the map and the
     * key ties the entry's value on the way to it. The comparison itself was read.
     */
    private static boolean readSaveForWhatTheOtherValueReaches(String report) {
        return report.lines().filter(line -> line.strip().startsWith("· not read"))
                .allMatch(line -> line.contains("not shown to reach every value here"));
    }

    /** What the model answers, as the operations are defined. */
    private static boolean oneMore(String key, Map<String, Long> entries, long q) {
        Long held = entries.get(key);
        return (held == null ? 0 : held + 1) >= q;
    }

    @Test
    void whetherTheListMadeOfTheEntryHoldsAnythingIsRead() {
        for (String model : List.of(OWN, MATCHED)) {
            String report = report(model);

            assertFalse(report.contains("not read"), report);
            assertTrue(report.contains("measurement: complete"), report);
        }
    }

    /**
     * A list of one holds something wherever the arm that made it is taken, so the arm that holds
     * nothing is the only way the condition fails, and no third rule stands for the list the
     * closure made being empty.
     */
    @Test
    void noRuleStandsForTheListOfOneBeingEmpty() {
        String report = report(MATCHED);

        assertTrue(report.contains("decision    rules 2"), report);
    }

    /** The closure's answer and not the entry's value: the same lines the arithmetic written
     *  under the arm draws. */
    @Test
    void theValueIsWhatTheClosureMadeOfTheEntry() {
        String mapped = report(ONE_MORE);
        String written = report(ONE_MORE_WRITTEN_OUT);

        assertEquals(linesAbout(written, "read as"), linesAbout(mapped, "read as"), mapped);
        assertTrue(mapped.contains("read as f/m[*]: = q - 1"), mapped);
        assertFalse(mapped.contains("read as f/m[*]: = q\n"), mapped);
    }

    /**
     * Every row offered for a line of the entry files a value under the key, and the value there
     * is where the line puts it; every row offered for the default files none.
     */
    @Test
    void aRowOfferedForTheEntryFilesItUnderTheKeyTheLookupAsks() {
        List<Row> rows = offered(ONE_MORE);

        assertEquals(8, rows.size(), rows::toString);
        for (Row row : rows) {
            if (row.label().contains("m[*]")) {
                assertTrue(row.entries().containsKey(row.key()), row::toString);
                long value = row.entries().get(row.key());
                switch (row.label()) {
                    case "m[*] = q - 1" -> assertEquals(row.q() - 1, value, row::toString);
                    case "m[*] = q - 2" -> assertEquals(row.q() - 2, value, row::toString);
                    case "q - 1 < m[*]" -> assertTrue(row.q() - 1 < value, row::toString);
                    case "m[*] < q - 2" -> assertTrue(value < row.q() - 2, row::toString);
                    default -> throw new AssertionError("a line nobody expected: " + row);
                }
            } else {
                assertFalse(row.entries().containsKey(row.key()), row::toString);
            }
        }
    }

    /** The rows offered, answered as the operations are defined, are all the model asks. */
    @Test
    void theRowsOfferedAreAnsweredByTheDefinitionAndSatisfyTheModel() {
        StringBuilder examples = new StringBuilder("\nexample f\n");
        for (Row row : offered(ONE_MORE)) {
            examples.append("    | \"").append(row.label()).append("\" : (")
                    .append(String.join(", ", row.inputTexts())).append(") -> ")
                    .append(oneMore(row.key(), row.entries(), row.q())).append('\n');
        }
        Compilation answered = measured(ONE_MORE + examples);

        assertEquals(List.of(), answered.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                () -> examples + report(answered));
        assertFalse(report(answered).contains("adequacy: not satisfied"),
                () -> report(answered));
        assertTrue(readSaveForWhatTheOtherValueReaches(report(answered)),
                () -> report(answered));
    }

    /** What the closure answers turns on nothing it is handed, so no line is drawn on the entry:
     *  only whether there is one, and the threshold against each of the two values. */
    @Test
    void aClosureThatReadsNothingItIsHandedDrawsNoLineOnTheEntry() {
        String report = report(CONSTANT);

        assertTrue(linesAbout(report, "read as f/m").isEmpty(), report);
        assertTrue(report.contains("read as f/q: = 42"), report);
        assertTrue(report.contains("read as f/q: = 0"), report);
    }

    /** A row offered for a line of the value the closure answers files an entry under the key,
     *  and one offered for a line of the default files none. */
    @Test
    void aRowForTheClosuresValueFilesAnEntryAndOneForTheDefaultDoesNot() {
        Map<String, Boolean> filedFor = Map.of("q = 42", true, "q = 43", true, "43 < q", true,
                "0 < q < 42", true, "q = 0", false, "q = 1", false, "1 < q <= 42", false,
                "q < 0", false);
        List<Row> rows = offered(CONSTANT);

        assertEquals(filedFor.keySet(), rows.stream().map(Row::label)
                .collect(Collectors.toSet()), rows::toString);
        for (Row row : rows) {
            assertEquals(filedFor.get(row.label()), row.entries().containsKey(row.key()),
                    row::toString);
        }
    }

    /**
     * The closure and the option are read where they stand, which is not where the arm is
     * wherever they were reached through a name, a binding or a helper's body: a function named
     * at the call, an option bound before it is matched, and the application written inside a
     * helper the body calls all draw the lines the closure written at the call draws.
     */
    @Test
    void whatTheClosureMadeIsReadWhereverTheClosureAndTheOptionStand() {
        List<String> written = linesAbout(report(ONE_MORE), "read as");
        for (String model : List.of("""
                module p
                behavior f : (k: String, m: Map<String, Int>, q: Int) -> Bool
                let inc (x: Int): Int = x + 1
                let f (k, m, q) = (Map.get(k, m) |> Option.map(inc) |> Option.withDefault(0)) >= q
                """, """
                module p
                behavior f : (k: String, m: Map<String, Int>, q: Int) -> Bool
                let f (k, m, q) = {
                    let r = Option.map(x -> x + 1, Map.get(k, m))
                    match r with
                        | Some v -> v >= q
                        | None -> 0 >= q
                }
                """, """
                module p
                behavior f : (k: String, m: Map<String, Int>, q: Int) -> Bool
                let plusOne (o: Option<Int>): Option<Int> = Option.map(x -> x + 1, o)
                let f (k, m, q) = (plusOne(Map.get(k, m)) |> Option.withDefault(0)) >= q
                """)) {
            String report = report(model);

            assertTrue(readSaveForWhatTheOtherValueReaches(report), report);
            assertEquals(written, linesAbout(report, "read as"), report);
        }
    }

    /**
     * A closure applied to the value an optional of the input holds is applied where it holds one,
     * and to that value: a comparison in it is a line on the optional's value, and is reached
     * where the optional holds one. An option is no container whose elements are counted, and
     * read as one there is no position for the element it was taken to have.
     */
    @Test
    void aClosureIsAppliedToTheValueAnOptionalOfTheInputHolds() {
        for (String body : List.of(
                "Option.withDefault(false, Option.map((v) -> v > 0, h.n))",
                "match Option.map((v) -> v > 0, h.n) with\n"
                        + "        | Some b -> b\n        | None -> false",
                "Option.withDefault(0, Option.map((v) -> if v > 0 then 1 else 0, h.n)) >= h.q")) {
            String report = report("""
                    module p
                    data H = { n: Option<Int>, q: Int }
                    behavior f : (h: H) -> Bool
                    let f (h) = %s
                    """.formatted(body));

            assertTrue(readSaveForWhatTheOtherValueReaches(report), report);
            assertTrue(report.contains("read as f/h.n@Some: = 1"), report);
            assertTrue(report.contains("read as f/h.n@Some: = 0"), report);
            assertFalse(report.contains("h.n[*]"), report);
        }
    }

    private static final String A_FIELD_AGAINST_A_STRING = """
            module p
            data Node = { holder: String }
            behavior f : (k: String, m: Map<String, Node>) -> Bool
            let f (k, m) = (Map.get(k, m) |> Option.map(n -> n.holder) |> Option.withDefault(""))
                == "x"
            """;

    /**
     * A field of the entry's value, compared with a string: the closure's answer is the field, and
     * the default is a string written out that the comparison settles alone. The line is on the
     * field of the entry under the key.
     */
    @Test
    void aFieldOfTheEntryComparedWithAStringIsALineOnTheField() {
        String report = report(A_FIELD_AGAINST_A_STRING);

        assertFalse(report.contains("not read"), report);
        assertTrue(report.contains("measurement: complete"), report);
        assertTrue(report.contains("read as f/m[*].holder: = x"), report);
        assertTrue(report.contains("decision    rules 1"), report);
        assertFalse(report.contains("nothing could show a row can be written"), report);
    }

    /** A row offered for the line on the field files the entry under the key. */
    @Test
    void aRowOfferedForTheFieldFilesTheEntryUnderTheKey() {
        Compilation compilation = measured(A_FIELD_AGAINST_A_STRING);
        Generator.GenerationResult result =
                OfferedAtTheLines.of(compilation, compilation.modules().get(0), "f");
        Pattern entry = Pattern.compile("\\(\"([^\"]*)\", Node \\{ holder = \"([^\"]*)\" \\}\\)");

        assertEquals(List.of(), result.unresolved());
        assertFalse(result.rows().isEmpty());
        for (Generator.GeneratedRow row : result.rows()) {
            List<String> texts = row.inputs().stream().map(FixtureTemplate::text).toList();
            String key = texts.get(0).substring(1, texts.get(0).length() - 1);
            Map<String, String> holders = new LinkedHashMap<>();
            Matcher each = entry.matcher(texts.get(1));
            while (each.find()) {
                holders.put(each.group(1), each.group(2));
            }
            String label = row.purposes().stream()
                    .filter(Generator.Purpose.ForAPoint.class::isInstance)
                    .map(point -> ((Generator.Purpose.ForAPoint) point).label())
                    .findFirst().orElseThrow();
            if (label.equals("m[*].holder = x")) {
                assertEquals("x", holders.get(key), texts::toString);
            } else {
                assertTrue(holders.containsKey(key), texts::toString);
                assertFalse("x".equals(holders.get(key)), texts::toString);
            }
        }
    }

    /** Two closures applied one after the other are both read: what the second made of what the
     *  first made of the entry. */
    @Test
    void twoClosuresAreReadOneAfterTheOther() {
        String report = report(TWICE);

        assertTrue(readSaveForWhatTheOtherValueReaches(report), report);
        assertTrue(report.contains("read as f/2 * m[*] - q: = -1"), report);
    }

    /** An option at a position of the input is that position, narrowed to its value. */
    @Test
    void anOptionAtAPositionIsThePositionsValue() {
        String report = report(AT_A_POSITION);

        assertTrue(readSaveForWhatTheOtherValueReaches(report), report);
        assertTrue(report.contains("read as f/h.qty@Some: = h.q - 1"), report);
    }

    /** A comparison inside the closure is about the value it is handed, as the same comparison
     *  under an arm opening the option is. */
    @Test
    void aComparisonInsideTheClosureIsAboutWhatTheOptionHolds() {
        String mapped = report(INSIDE_THE_CLOSURE);
        String written = report(INSIDE_THE_ARM);

        assertEquals(linesAbout(written, "read as f/m[*]"), linesAbout(mapped, "read as f/m[*]"),
                mapped);
        assertTrue(mapped.contains("read as f/m[*]: = 1"), mapped);
    }

    /**
     * A row offered for a line of the comparison inside the closure files the value under the key
     * the lookup asks for: the closure is handed that entry's value, and not any value the map
     * holds.
     */
    @Test
    void aRowOfferedForTheComparisonInsideTheClosureFilesItUnderTheKey() {
        // The comparison inside the closure and the one over what it made draw the same lines, and
        // each is offered its rows.
        List<Row> rows = offered(INSIDE_THE_CLOSURE).stream()
                .filter(row -> row.label().contains("m[*]")).toList();

        assertEquals(Set.of("m[*] = 1", "m[*] = 0", "1 < m[*]", "m[*] < 0"),
                rows.stream().map(Row::label).collect(Collectors.toSet()), rows::toString);
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

    /**
     * Whether a row stands at a point of a line is asked of the entry under the key the lookup
     * asks for. Another key holding the value at the point puts no row there: the row whose
     * looked-up entry is above the line leaves the point on it undecided, wherever the other entry
     * is.
     */
    @Test
    void anotherKeyHoldingTheValueAtAPointPutsNoRowThere() {
        List<String> underTheKey = undecidedAfter(INSIDE_THE_CLOSURE,
                "(\"A\", [(\"A\", 1)]) -> true");
        List<String> underAnother = undecidedAfter(INSIDE_THE_CLOSURE,
                "(\"A\", [(\"B\", 1), (\"A\", 5)]) -> true");

        assertFalse(underTheKey.contains("ON"), underTheKey::toString);
        assertTrue(underAnother.contains("ON"), underAnother::toString);
    }

    /** The same of a value the closure made, read under the arm that opens it. */
    @Test
    void anotherKeyHoldingTheValueAtAPointOfWhatTheClosureMadePutsNoRowThere() {
        List<String> underTheKey = undecidedAfter(ONE_MORE,
                "(\"A\", [(\"A\", 4)], 5) -> true");
        List<String> underAnother = undecidedAfter(ONE_MORE,
                "(\"A\", [(\"B\", 4), (\"A\", 9)], 5) -> true");

        assertFalse(underTheKey.contains("ON"), underTheKey::toString);
        assertTrue(underAnother.contains("ON"), underAnother::toString);
    }

    /** The points of the lines of the entry {@code row} leaves undecided, by the word the report
     *  uses. */
    private static List<String> undecidedAfter(String model, String row) {
        String report = report(measured(model + """

                example f
                    | "one row" : %s
                """.formatted(row)));
        assertTrue(report.contains("read as f/m[*]"), report);
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

    /** What the closure makes is read where nothing says what the value it is handed is: a list
     *  of none holds nothing, and the default the option leaves holds something. */
    @Test
    void whatTheClosureMakesIsReadOfAValueNothingIsKnownOf() {
        for (String model : List.of("""
                module p
                behavior f : (xs: List<Int>) -> Bool
                let f (xs) = Bool.not(List.isEmpty(
                    List.find(x -> x > 0, xs) |> Option.map(one -> [ one ]) |> Option.withDefault([])))
                """, """
                module p
                behavior f : (k: String, m: Map<String, Int>) -> Bool
                let f (k, m) = Bool.not(List.isEmpty(
                    Map.get(k, m) |> Option.map(one -> []) |> Option.withDefault([ 0 ])))
                """)) {
            String report = report(model);

            assertFalse(report.contains("not read"), report);
            assertTrue(report.contains("measurement: complete"), report);
        }
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
            out.add(new Row(label, texts, key, entries,
                    texts.size() > 2 ? Long.parseLong(texts.get(2)) : 0));
        }
        assertEquals(List.of(), result.unresolved(), "every point is offered a row");
        return out;
    }
}
