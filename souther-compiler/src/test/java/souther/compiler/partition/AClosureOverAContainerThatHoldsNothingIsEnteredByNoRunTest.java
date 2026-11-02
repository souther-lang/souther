package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A closure an operation applies over a container that no position holds is entered where what
 * the library says of the operation that made the container holding something holds, and nowhere
 * else.
 *
 * <p>Where that holds on no row, no run makes the comparisons in the closure, and nothing is left
 * unread of them: they divide nothing, which is what the program does. Where it holds on some row,
 * or nothing says on which, the comparisons are read as they were. And the container is still
 * worked out: an operation that may stop a run while making it stops it whether or not the
 * closure is applied to anything.
 */
class AClosureOverAContainerThatHoldsNothingIsEnteredByNoRunTest {

    @Test
    void aComparisonOverNothingTakenLeavesNothingUnread() {
        List<String> report = report("email: String, d: String",
                "List.any(p -> p == d, List.take(0, String.split(\"@\", email)))");
        assertEquals(List.of(), unread(report), report.toString());
        assertTrue(report.contains("· divided no way: d"), report.toString());
        assertTrue(report.getFirst().endsWith("measurement: complete"), report.toString());
    }

    /** A list of every whole number between two that ends below where it starts is empty too, an
     *  end the input holds below the other included. */
    @Test
    void aComparisonOverARangeThatEndsBelowItsStartLeavesNothingUnread() {
        List<String> report = report("d: Int, k: Int",
                "List.any(p -> p == d, List.rangeInclusive(k + 1, k))");
        assertEquals(List.of(), unread(report), report.toString());
        assertTrue(report.contains("· divided no way: d"), report.toString());
    }

    @Test
    void aComparisonOverSomethingTakenIsReadAsBefore() {
        List<String> report = report("email: String, d: String",
                "List.any(p -> p == d, List.take(1, String.split(\"@\", email)))");
        assertEquals(List.of(
                "· no line: comparison@3:36 — it relates the value here to another value rather"
                        + " than dividing the values here, about `email`",
                "· not read: comparison@3:36 — what it states was read, and it relates the value"
                        + " here to another value; its classes hold the values it was shown over,"
                        + " and the rest are shown on neither side of it, about `d`"),
                unread(report));
    }

    /** How many are taken being the input's, nothing shows the closure is applied to none. */
    @Test
    void aCountNothingFixesShowsNoComparisonUnmade() {
        List<String> report = report("email: String, d: String, n: Int",
                "List.any(p -> p == d, List.take(n, String.split(\"@\", email)))");
        assertEquals(List.of("· not read: comparison@3:39 — written in a form this compiler does"
                + " not read, about `d`"), unread(report));
    }

    /**
     * The list a closure is applied to none of is still made, and making it divides by {@code k}:
     * every row the comparison after it is owed is one whose run gets past the division.
     */
    @Test
    void whatMakesAnEmptyContainerStillStopsTheRun() {
        Compilation compilation = compiled("k: Int, d: Int",
                "List.any(p -> p == d, List.take(0, [100 / k])) || d > 3");
        List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), "w1").get("m");
        assertNotNull(lines, "m was measured");
        assertEquals(List.of("3"), lines.stream().map(BorderAssessment::value).toList());
        List<List<String>> rows = new ArrayList<>();
        for (BorderAssessment border : lines) {
            for (ItemAssessment item : border.items().values()) {
                if (item instanceof ItemAssessment.Owed owed) {
                    for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                        if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                            rows.add(certified.row().inputs().stream()
                                    .map(each -> each.text()).toList());
                        }
                    }
                }
            }
        }
        assertFalse(rows.isEmpty(), "the line is owed rows");
        for (List<String> row : rows) {
            assertTrue(Long.parseLong(row.getFirst()) != 0, "a run past the division: " + row);
        }
    }

    /** The division making the list is what a row gets past to the comparison after it: it ties
     *  {@code k}, which a division by a number written down does not. */
    @Test
    void theDivisionAnEmptyContainerIsMadeOfIsGotPastOnTheWayOn() {
        assertEquals(List.of(new DemandReading.Tie(Set.of(TermPath.of("k")), null)),
                gotPastAtTheLast("List.any(p -> p == d, List.take(0, [100 / k])) || d > 3")
                        .tied());
        assertEquals(List.of(),
                gotPastAtTheLast("List.any(p -> p == d, List.take(0, [100 / 5])) || d > 3")
                        .tied());
    }

    /** The end of an empty range is still worked out: a row past {@code k + 1} has {@code k}
     *  below the greatest, and a row past {@code k - 1} has it above the least. */
    @Test
    void theEndOfAnEmptyRangeIsGotPastOnTheWayOn() {
        assertEquals(List.of(new TakenConstraint.Affine(LinearForm.<NumericTerm>atom(K)
                        .plus(LinearForm.constant(ExactRatio.of(MOST.negate())))
                        .orNull(), Rel.LE)),
                gotPastAtTheLast("List.any(p -> p == d, List.rangeInclusive(k + 1, k)) || d > 3")
                        .narrowing());
        assertEquals(List.of(new TakenConstraint.Affine(LinearForm.<NumericTerm>atom(K)
                        .plus(LinearForm.constant(ExactRatio.of(LEAST.negate())))
                        .orNull(), Rel.GE)),
                gotPastAtTheLast("List.any(p -> p == d, List.rangeInclusive(k, k - 1)) || d > 3")
                        .narrowing());
    }

    private static final NumericTerm K = new NumericTerm.ValueOf(TermPath.of("k"));

    /** One below the greatest {@code Int}, the most {@code k + 1} is worked out at. */
    private static final BigInteger MOST = BigInteger.valueOf(Long.MAX_VALUE - 1);

    /** One above the least, the least {@code k - 1} is worked out at. */
    private static final BigInteger LEAST = BigInteger.valueOf(Long.MIN_VALUE + 1);

    /** What a row gets past to the last comparison of {@code m (k: Int, d: Int) = body}. */
    private static DemandReading.Answered gotPastAtTheLast(String body) {
        Compilation compilation = compiled("k: Int, d: Int", body);
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("m");
        AnalysisBody analysis = checked.analysisBodies().get("m");
        List<ComparisonReadings.Reading> readings = ComparisonReadings.of("m", analysis,
                inputs.reading(rules),
                InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                        inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        inputs.dependencies()),
                CountWitnesses.AtComparisons.NONE).comparisons();
        assertEquals(2, readings.size(), readings::toString);
        return readings.getLast().getsPast();
    }

    /** The lines that say a comparison was left unread or relates rather than divides. */
    private static List<String> unread(List<String> report) {
        return report.stream()
                .filter(line -> line.startsWith("· not read") || line.startsWith("· no line"))
                .toList();
    }

    private static List<String> report(String parameters, String body) {
        Compilation compilation = compiled(parameters, body);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).toList();
    }

    private static Compilation compiled(String parameters, String body) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior m : (%s) -> Bool
                let m (%s) = %s
                """.formatted(parameters, parameters.replaceAll(":\\s*[A-Za-z]+", ""), body),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
