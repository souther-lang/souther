package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A boundary a guard draws is met by the row that reached the comparison, which no arm can say.
 *
 * <p>Under {@code A && B} the {@code else} arm is where a row that made {@code B} false lands and
 * where a row that never got to {@code B} lands. So an arm hit is neither necessary nor sufficient
 * evidence that a particular comparison produced a value, and a measure that reads one for the other
 * is wrong in both directions: it credits a row that skipped the comparison, and it cannot credit a
 * row that ran it.
 *
 * <p>Two positions, so that the operand in front of the boundary's own comparison can be made false
 * independently of it. With one position the two cannot be told apart in a row at all.
 */
class AnArmDoesNotSayWhetherAComparisonRanTest {

    private static final String MODULE = "example.gate";

    private static final String MODEL = """
            module example.gate

            data Request = { rank: Int, cost: Int }

            data Auto
            data Manual

            behavior gate : (r: Request) -> Auto | Manual
                constructs Auto, Manual
            let gate (r) =
                if r.rank >= 0 && r.cost <= 100000 then Auto else Manual

            example gate
                | "one row" : (Request { rank = RANK, cost = COST }) -> OUT
            """;

    /** Every line of {@code gate}, as measured against the one row this model has. */
    private static List<BorderAssessment> linesFor(String rank, String cost, String out) {
        Compilation compilation = Compilation.ofSource(
                MODEL.replace("RANK", rank).replace("COST", cost).replace("OUT", out), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                compilation.db().ask(new Adequacy.Boundaries(MODULE)).value();
        assertNotNull(boundaries, "the model under test compiles");
        return boundaries.get("gate");
    }

    /** The points against the lines of {@code gate}, which is what a row at a value is owed for. */
    private static List<BorderAssessment.Point> pointsFor(String rank, String cost, String out) {
        return BorderAssessment.pointsOf(linesFor(rank, cost, out)).stream()
                .filter(p -> p.role().againstTheLine()).filter(p -> p.owed() != null).toList();
    }

    /** What the rows established about one line, named the way a report names it. */
    private static ItemAssessment.Coverage coverageOf(List<BorderAssessment> lines,
                                                          String axis, String value) {
        return BorderAssessment.pointsOf(lines).stream()
                .filter(p -> p.role().againstTheLine()).filter(p -> p.owed() != null)
                .filter(p -> p.border().axis().equals(axis) && value.equals(p.against()))
                .findFirst()
                .orElseThrow(() -> new AssertionError(
                        "no line at " + axis + " = " + value + " among " + labels(lines)))
                .owed().coverage();
    }

    private static List<String> labels(List<BorderAssessment> lines) {
        return BorderAssessment.pointsOf(lines).stream()
                .filter(p -> p.role().againstTheLine()).filter(p -> p.owed() != null)
                .map(p -> p.border().axis() + " = " + p.against()).toList();
    }

    /**
     * The pair that settles it: one value, one arm, two answers.
     *
     * <p>Both rows write 100001 and both land in {@code else}. One made {@code r.cost <= 100000}
     * false to get there and the other never reached it, and the edge is met by the first and not by
     * the second. Everything an arm records is the same between them, so nothing read off the arms
     * can tell them apart — which is why the comparison is observed where it runs.
     */
    @Test
    void oneValueAndOneArmAreNotOneAnswer() {
        assertEquals(new ItemAssessment.Coverage.Hit(),
                coverageOf(linesFor("0", "100001", "Manual"), "gate/r.cost", "100001"),
                "the comparison produced false, which is reaching it");
        assertEquals(new ItemAssessment.Coverage.Missed(),
                coverageOf(linesFor("-1", "100001", "Manual"), "gate/r.cost", "100001"),
                "the comparison never ran, and the row lands in the same arm");
    }

    /** A row that reached the comparison and made it true meets the line's own value. */
    @Test
    void aRowThatMadeTheComparisonTrueMeetsTheValue() {
        assertEquals(new ItemAssessment.Coverage.Hit(),
                coverageOf(linesFor("0", "100000", "Auto"), "gate/r.cost", "100000"));
    }

    /**
     * A row that never reached the comparison does not meet it, however it reads.
     *
     * <p>The row writes the boundary value and lands in {@code else}, which is the whole of what the
     * arms record — and {@code r.cost <= 100000} did not run, because {@code r.rank >= 0} settled the
     * condition first.
     */
    @Test
    void aRowThatSkippedTheComparisonDoesNotMeetTheValue() {
        assertEquals(new ItemAssessment.Coverage.Missed(),
                coverageOf(linesFor("-1", "100000", "Manual"), "gate/r.cost", "100000"));
    }

    /**
     * Every line of this guard is one the rows can be measured against.
     *
     * <p>Four of them — each cut and the neighbour on its other side — and none waiting on an arm to
     * witness it. Asked over the whole list rather than of the one line the other tests name, so that
     * a line quietly dropped shows up here as a count.
     */
    @Test
    void everyLineIsMeasured() {
        List<BorderAssessment> lines = linesFor("0", "100001", "Manual");

        assertEquals(List.of("gate/r.rank = 0", "gate/r.rank = -1",
                        "gate/r.cost = 100000", "gate/r.cost = 100001"),
                labels(lines));
        for (BorderAssessment.Point line : pointsFor("0", "100001", "Manual")) {
            assertNull(line.item().whyNotMeasured(), line.label() + " was measured");
        }
    }

    /** And the new observation is not an arm: the branch measure counts the two arms it always
     * counted. */
    @Test
    void theComparisonIsNotCountedAsAnArm() {
        Compilation compilation = Compilation.ofSource(
                MODEL.replace("RANK", "0").replace("COST", "100001").replace("OUT", "Manual"),
                "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, Adequacy.BranchEvidence> branches =
                compilation.db().ask(new Adequacy.BranchCoverage(MODULE)).value();
        assertNotNull(branches, "the model under test compiles");

        assertEquals(List.of("then", "else"),
                branches.get("gate").all().stream()
                        .map(souther.compiler.report.ArmVocabulary::label).toList());
    }
}
