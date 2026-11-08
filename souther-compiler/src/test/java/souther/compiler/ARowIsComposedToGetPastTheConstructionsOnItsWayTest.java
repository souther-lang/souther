package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A row composed for a decision rule gets past every construction on the rule's way: the clauses of
 * the invariant of each type the way builds are asked of the row as the way's conditions are, so a
 * body building a state whose invariant asks for an element is offered a row holding one, and a
 * value of a sum the invariant refuses one case of is offered the other. A clause over the
 * elements of what the construction is handed is read as the same clause written over the input,
 * whether the construction is attempted or not.
 *
 * <p>A way no input gets past is no rule a row is owed: the model's own rules leave it none.
 *
 * <p>Where every row composed still stops — at a construction whose clauses no composer here
 * writes a row for, at an {@code ensures}, at an operation the runtime will not finish — the report
 * says where each run stopped.
 */
class ARowIsComposedToGetPastTheConstructionsOnItsWayTest {

    private static final String GOT_PAST = """
            module aborts

            data Confirmed = { lines: List<Int> }
                invariant List.length(lines) >= 1

            behavior confirm : (lines: List<Int>) -> Confirmed
                constructs Confirmed
            let confirm (lines) = Confirmed { lines = lines }

            data Tagged = { tags: Set<Int> }
                invariant Set.size(tags) >= 2

            behavior tag : (tags: Set<Int>) -> Tagged
                constructs Tagged
            let tag (tags) = Tagged { tags = tags }

            data Labelled = { label: String }
                invariant String.length(label) >= 3

            behavior label : (label: String) -> Labelled
                constructs Labelled
            let label (label) = Labelled { label = label }

            data Bag = List<Int>

            data Packed = { bag: Bag }
                invariant List.length(bag.value) >= 1

            behavior pack : (bag: Bag) -> Packed
                constructs Packed
            let pack (bag) = Packed { bag = bag }

            data Floored = { n: Int }
                invariant n >= 5

            let floored (n: Int): Floored = Floored { n = n }

            behavior floor : (n: Int) -> Floored
                constructs Floored
            let floor (n) = floored(n)

            data Red
            data Green
            data Colour = Red | Green

            data Lit = { c: Colour }
                invariant match c with
                    | Green -> true
                    | Red -> false

            behavior light : (c: Colour) -> Lit
                constructs Lit
            let light (c) = Lit { c = c }

            data Counts = { xs: List<Int> }
                invariant List.length(xs) >= 1 && List.all(x -> x >= 1, xs)

            behavior count : (xs: List<Int>) -> Counts
                constructs Counts
            let count (xs) = Counts { xs = xs }

            data Refused

            behavior attempt : (xs: List<Int>) -> Counts | Refused
                constructs Counts
            let attempt (xs) = if Counts { xs = xs } as counted then counted else Refused
            """;

    /** Each behavior and the row it is offered, which gets past its construction. */
    private static final Map<String, String> OFFERED = Map.of(
            "confirm", "([0])",
            "tag", "([0, 1])",
            "label", "(\"xxx\")",
            "pack", "(Bag([0]))",
            "floor", "(5)",
            "light", "(Green)",
            "count", "([1])",
            "attempt", "([1])");

    @Test
    void aRowIsComposedThatGetsPastTheConstructionOnItsWay() {
        Compilation compilation = compiled(GOT_PAST);
        String report = report(compilation);
        List<RowsOfABlock.Row> rows = RowsOfABlock.of(offered(compilation, "aborts"));

        List<String> failed = new ArrayList<>();
        for (Map.Entry<String, String> each : OFFERED.entrySet()) {
            List<String> written = rows.stream()
                    .filter(row -> row.behavior().equals(each.getKey()))
                    .map(RowsOfABlock.Row::written).toList();
            if (written.stream().noneMatch(row -> row.replaceAll("\\s+", " ")
                    .contains(each.getValue() + " -> <?>"))) {
                failed.add(each.getKey() + " is offered " + written);
            }
        }
        assertEquals(List.of(), failed);
        assertEquals(List.of(), report.lines().filter(line -> line.contains("? ")).toList(),
                report);
        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    /** {@code b} false is a way no input gets past, so the body has one rule and not two. */
    @Test
    void aWayNoInputGetsPastIsNoRule() {
        Compilation compilation = compiled("""
                module truth

                data Yes = { b: Bool }
                    invariant b

                behavior say : (b: Bool) -> Yes
                    constructs Yes
                let say (b) = Yes { b = b }
                """);

        assertEquals(List.of("    decision    rules 1   taken 0"), report(compilation).lines()
                .filter(line -> line.contains("decision    rules")).toList());
    }

    private static final String STOPPED = """
            module stops

            data Pos = { n: Int }
                invariant n >= 1

            behavior square : (n: Int) -> Pos
                constructs Pos
            let square (n) = Pos { n = n * n - 1 }

            data Out = { n: Int }

            behavior grow : (n: Int) -> Out
                constructs Out
                ensures grows = value.n >= n
            let grow (n) = Out { n = n * n - 1 }

            behavior overflow : (n: Int) -> Out
                constructs Out
            let overflow (n) = Out { n = 9223372036854775807 + 1 - n }
            """;

    @Test
    void whereEveryRowComposedStopsTheReportSaysWhere() {
        Compilation compilation = compiled(STOPPED);
        String report = report(compilation);
        String source = compilation.sourceIdOf("stops").value();

        assertEquals(List.of(
                undecided("the construction at " + at(source, "Pos { n = n * n")
                        + ", where invariant Pos #1 did not hold"),
                undecided("the answer, where ensures grow (grows) did not hold"),
                undecided("an operation the runtime would not finish (Int overflow:"
                        + " 9223372036854775807 + 1)")),
                report.lines().filter(line -> line.contains("? nothing could show")).toList(),
                report);
    }

    /** The document says the same places, in its own words, and is shaped as its schema says. */
    @Test
    void theDocumentSaysWhereEveryRowComposedStopped() {
        Compilation compilation = compiled(STOPPED);
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        String source = compilation.sourceIdOf("stops").value();
        int at = STOPPED.indexOf("Pos { n = n * n");
        String before = STOPPED.substring(0, at);

        assertEquals(List.of(
                JSON.readTree("""
                        [{"at": "a_construction", "rule": "invariant Pos #1",
                          "module": "stops", "declaredIn": "stops",
                          "sourceId": "%s", "line": %d, "column": %d}]""".formatted(source,
                        (int) before.chars().filter(c -> c == '\n').count() + 1,
                        at - before.lastIndexOf('\n'))),
                JSON.readTree("""
                        [{"at": "an_ensures", "rule": "ensures grow (grows)",
                          "module": "stops", "declaredIn": "stops"}]"""),
                JSON.readTree("""
                        [{"at": "an_end",
                          "said": "Int overflow: 9223372036854775807 + 1"}]""")),
                List.of(stoppedOf(document, "square"), stoppedOf(document, "grow"),
                        stoppedOf(document, "overflow")));
    }

    /** What the document says the runs of {@code behavior}'s one decision rule stopped at. */
    private static JsonNode stoppedOf(JsonNode document, String behavior) {
        for (JsonNode each : document.path("modules").get(0).path("behaviors")) {
            if (each.path("name").asString().equals(behavior)) {
                return each.path("decision").path("obligations").get(0)
                        .path("synthesisShortfalls").get(0).path("runsStopped");
            }
        }
        throw new AssertionError("the document says nothing of " + behavior + ": " + document);
    }

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static String undecided(String stoppedAt) {
        return "      ? nothing could show a row can be written at a decision rule — no row"
                + " composed here was run to an answer, and the runs stopped at " + stoppedAt;
    }

    /** {@code source}, and the line and column {@code construction} starts at in the model. */
    private static String at(String source, String construction) {
        int at = STOPPED.indexOf(construction);
        String before = STOPPED.substring(0, at);
        int line = (int) before.chars().filter(c -> c == '\n').count() + 1;
        int column = at - before.lastIndexOf('\n');
        return source + ":" + line + ":" + column;
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(e -> e.diagnostic().code().toString()).toList());
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String offered(Compilation compilation, String module) {
        return GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule(module)),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).textInEnglish();
    }
}
