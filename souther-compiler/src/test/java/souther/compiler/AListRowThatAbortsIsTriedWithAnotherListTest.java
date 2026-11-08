package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A row composed for a decision rule whose run stops at a construction is tried again with another
 * value of the same class. A value holding elements is displaced by one element more than the least
 * its rules let it hold, as a number is by one, so a body building a state whose invariant asks for
 * an element is offered a row holding one.
 *
 * <p>Where every value tried stops, the report says where: the construction, by the source and the
 * line and column it starts at, and the clause of its type's invariant that did not hold, numbered
 * as the declaration counts its clauses or named where it has a name.
 */
class AListRowThatAbortsIsTriedWithAnotherListTest {

    private static final String DISPLACED = """
            module aborts

            data Confirmed = { lines: List<Int> }
                invariant List.length(lines) >= 1

            behavior confirm : (lines: List<Int>) -> Confirmed
                constructs Confirmed
            let confirm (lines) = Confirmed { lines = lines }

            data Tagged = { tags: Set<Int> }
                invariant Set.size(tags) >= 1

            behavior tag : (tags: Set<Int>) -> Tagged
                constructs Tagged
            let tag (tags) = Tagged { tags = tags }

            data Indexed = { index: Map<String, Int> }
                invariant Map.size(index) >= 1

            behavior file : (index: Map<String, Int>) -> Indexed
                constructs Indexed
            let file (index) = Indexed { index = index }

            data Labelled = { label: String }
                invariant String.length(label) >= 1

            behavior label : (label: String) -> Labelled
                constructs Labelled
            let label (label) = Labelled { label = label }

            data Bag = List<Int>

            data Packed = { bag: Bag }
                invariant List.length(bag.value) >= 1

            behavior pack : (bag: Bag) -> Packed
                constructs Packed
            let pack (bag) = Packed { bag = bag }

            data Nested = { groups: List<List<Int>> }
                invariant List.length(groups) >= 1

            behavior group : (groups: List<List<Int>>) -> Nested
                constructs Nested
            let group (groups) = Nested { groups = groups }
            """;

    /** Each behavior and the row it is offered: one element where none was the first value. */
    private static final Map<String, String> OFFERED = Map.of(
            "confirm", "([0])",
            "tag", "([0])",
            "file", "([(\"x\", 0)])",
            "label", "(\"x\")",
            "pack", "(Bag([0]))",
            "group", "([[]])");

    @Test
    void aContainerTheFirstRowStopsAtIsTriedHoldingOneElementMore() {
        Compilation compilation = compiled(DISPLACED);
        String report = report(compilation);
        List<RowsOfABlock.Row> rows = RowsOfABlock.of(offered(compilation, "aborts"));

        List<String> failed = new ArrayList<>();
        for (Map.Entry<String, String> each : OFFERED.entrySet()) {
            List<String> written = rows.stream()
                    .filter(row -> row.behavior().equals(each.getKey()))
                    .map(RowsOfABlock.Row::written).toList();
            if (written.size() != 1 || !written.getFirst().contains(each.getValue() + " -> <?>")) {
                failed.add(each.getKey() + " is offered " + written);
            }
        }
        assertEquals(List.of(), failed);
        assertEquals(OFFERED.size(), report.lines()
                .filter(line -> line.contains("! no row takes a decision rule")).count(), report);
        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    private static final String STOPPED = """
            module stops

            data Pair = { lines: List<Int> }
                invariant List.length(lines) <= 10
                invariant List.length(lines) >= 2

            behavior couple : (lines: List<Int>) -> Pair
                constructs Pair
            let couple (lines) = Pair { lines = lines }

            data Counted = { n: Int }
                invariant atLeastTwo = n >= 2

            behavior tally : (n: Int) -> Counted
                constructs Counted
            let tally (n) = Counted { n = n }
            """;

    @Test
    void whereEveryValueTriedStopsTheReportNamesTheConstructionAndTheClause() {
        Compilation compilation = compiled(STOPPED);
        String report = report(compilation);
        String source = compilation.sourceIdOf("stops").value();

        assertEquals(List.of(
                undecided(source, "Pair { lines", "invariant Pair #2"),
                undecided(source, "Counted { n", "invariant Counted (atLeastTwo)")),
                report.lines().filter(line -> line.contains("? nothing could show")).toList(),
                report);
    }

    /** The line a rule is left undecided with, where every run stopped at the construction
     *  starting with {@code construction} and {@code clause} did not hold. */
    private static String undecided(String source, String construction, String clause) {
        int at = STOPPED.indexOf(construction);
        String before = STOPPED.substring(0, at);
        int line = (int) before.chars().filter(c -> c == '\n').count() + 1;
        int column = at - before.lastIndexOf('\n');
        return "      ? nothing could show a row can be written at a decision rule — no row"
                + " composed here was run to an answer, and the runs stopped at the construction"
                + " at " + source + ":" + line + ":" + column + ", where " + clause
                + " did not hold";
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
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String offered(Compilation compilation, String module) {
        return GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule(module)),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }
}
