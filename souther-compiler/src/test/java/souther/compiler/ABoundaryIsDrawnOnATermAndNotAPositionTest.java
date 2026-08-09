package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BoundaryAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a boundary is drawn on is a number a rule compares, and where that number is read from is a
 * property of the term rather than of the position.
 *
 * <p>A newtype's own value is one such number. So is the length of a string and the size of a
 * container, which the discharge procedure has always named the same way (spec
 * §invariant-discharge-terms). Read as positions they are not numbers at all, and every position
 * holding one came back as a place the model draws no line through — said of a position whose own
 * type bounds it, and said again of one the body compares in the line above.
 */
class ABoundaryIsDrawnOnATermAndNotAPositionTest {

    /**
     * One model stating the same bound four ways, and a numeric one beside them to be read against.
     *
     * <p>Beside them on purpose: what a length is owed is what a number is owed, and the way to say
     * so is to measure both in one run rather than to write down what each should say.
     */
    private static final String MODEL = """
            module example.terms

            data Label = String
                invariant nonEmpty = String.length(value) > 0

            data Names = List<String>
                invariant twoNames = List.length(value) >= 2

            data Codes = Set<String>
                invariant someCodes = Set.size(value) >= 1

            data Props = Map<String, String>
                invariant someProps = Map.size(value) >= 1

            data Size = Int
                invariant atLeastOne = value >= 1

            data T = { label: Label, names: Names, codes: Codes, props: Props, size: Size }

            behavior look : (t: T) -> Int
            let look (t) = t.size.value

            example look
                | (T { label = Label("a")
                     , names = Names([ "p", "q", "r" ])
                     , codes = Codes([ "c" ])
                     , props = Props([ ("k", "v") ])
                     , size = Size(1) }) -> 1
            """;

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    private static Map<String, PartitionEvidence> partitions(String source) {
        Compilation compilation = compiled(source);
        return compilation.db().ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
    }

    private static List<String> labels(PartitionEvidence partition) {
        return partition.boundaries().stream().map(BoundaryAssessment::label).sorted().toList();
    }

    /** A size call in an invariant draws the line its number names, and the line is named by the term
     * it was drawn on. */
    @Test
    void anInvariantOverASizeDrawsItsEdge() {
        assertEquals(List.of(
                        "List.length(t.names) = 2",
                        "Map.size(t.props) = 1",
                        "Set.size(t.codes) = 1",
                        "String.length(t.label) = 1",
                        "t.size = 1"),
                labels(partitions(MODEL).get("look")));
    }

    /** One obligation each, and at the edge. Everything outside an invariant is refused at
     * construction, so there is no row beyond it to ask for — which is what the numeric bound beside
     * them has always done. */
    @Test
    void anInvariantsEdgeIsOwedOnceAndNotOnBothSides() {
        for (BoundaryAssessment line : partitions(MODEL).get("look").boundaries()) {
            assertEquals(souther.compiler.partition.BoundaryObligation.BoundarySide.AT, line.side(),
                    line.label());
        }
    }

    /** The row is read through the term, so a row whose string is one character long is at the length
     * boundary and a row of three names is not at the one that wants two. */
    @Test
    void aRowIsReadThroughTheTermThatDrewTheLine() {
        Map<String, BoundaryAssessment> byLabel = new java.util.LinkedHashMap<>();
        partitions(MODEL).get("look").boundaries().forEach(b -> byLabel.put(b.label(), b));

        assertTrue(byLabel.get("String.length(t.label) = 1").coverage().hit(),
                "the row's label is one character long");
        assertTrue(byLabel.get("Set.size(t.codes) = 1").coverage().hit(),
                "the row's set holds one code");
        assertEquals(BoundaryAssessment.Coverage.Missed.class,
                byLabel.get("List.length(t.names) = 2").coverage().getClass(),
                "the row holds three names, and nothing was unreadable about it");
    }

    /** The report stops saying the model draws no line through a position its own type bounds. */
    @Test
    void noneOfThemIsReportedAsAPositionNothingDivides() {
        String human = AdequacyReport.of(compiled(MODEL)).human();
        assertFalse(human.contains("not derivable"), human);
    }

    private static final String GUARDED = """
            module example.guarded

            data Label = String
                invariant nonEmpty = String.length(value) > 0

            data T = { label: Label }

            behavior guarded : (t: T) -> Int
            let guarded (t) = {
                guard String.length(t.label.value) > 3 else 0
                1
            }

            example guarded
                | (T { label = Label("abcd") }) -> 1
            """;

    /**
     * A guard over the same term draws the same kind of line, and its own value has values on both
     * sides of it.
     *
     * <p>The invariant's edge is still there beside it: two rules at one position are two lines, and
     * a length is no different there either.
     */
    @Test
    void aGuardOverATermDrawsTheLineAndItsNeighbour() {
        assertEquals(List.of(
                        "String.length(t.label) = 1",
                        "String.length(t.label) = 3",
                        "String.length(t.label) = 4"),
                labels(partitions(GUARDED).get("guarded")));
    }

    /** And the position is measured, where before the body compared a number at a position the report
     * called undivided. */
    @Test
    void theGuardedPositionIsAnAxis() {
        PartitionEvidence partition = partitions(GUARDED).get("guarded");
        assertEquals(List.of("String.length(t.label)"),
                partition.axes().stream().map(PartitionEvidence.AxisCoverage::path).toList());
    }

    private static final String UNBOUNDED = """
            module example.unbounded

            data T = { names: List<String> }

            behavior atLeastNone : (t: T) -> Int
            let atLeastNone (t) = {
                guard List.length(t.names) >= 0 else 0
                1
            }

            example atLeastNone
                | (T { names = [] }) -> 1
            """;

    /**
     * A size is never negative, and the term says so rather than the rules that happen to be written
     * about it.
     *
     * <p>The guard's line is at zero and its neighbour below is minus one, which is a row nobody can
     * write. Nothing in this model states a lower bound, so what keeps that obligation from being
     * asked for is what the term knows about its own values.
     */
    @Test
    void aSizeIsNeverNegativeAndNoRowIsAskedForBelowZero() {
        assertEquals(List.of("List.length(t.names) = 0"),
                labels(partitions(UNBOUNDED).get("atLeastNone")));
    }
}
