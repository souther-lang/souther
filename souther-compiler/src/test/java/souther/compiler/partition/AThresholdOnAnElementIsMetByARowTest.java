package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A threshold an author wrote inside a closure is a line rows are owed either side of.
 *
 * <p>The model below writes one, and its rows are the ones the issue reports as passing a strict
 * build: one item under the threshold and one over it, and an empty list. Nothing among them is at
 * the threshold itself, so rewriting {@code >=} to {@code >} changed no answer any row could see and
 * a strict build stayed green over a behavior whose meaning had moved.
 *
 * <p>What settles it is that the two are now measured apart. The line falls at the element, the
 * points against it are the values either side, and the rows are held to reaching them.
 */
class AThresholdOnAnElementIsMetByARowTest {

    private static final String MODULE = "example.charges";

    private static final String MODEL = """
            module example.charges

            data Item = { charge: Int }
            data Total = Int

            behavior countOverThreshold : (items: List<Item>) -> Total
                constructs Total
            let countOverThreshold (items) =
                Total(List.length(List.filter(i -> i.charge OP 21000, items)))

            example countOverThreshold
                | "one under, one over" : ([ Item { charge = 1000 },
                                             Item { charge = 50000 } ]) -> Total(1)
                | "empty" : ([ ]) -> Total(0)
            """;

    /** Every point against the line of {@code countOverThreshold}, as the rows leave it. */
    private static List<BorderAssessment.Point> pointsFor(String operator) {
        Compilation compilation = Compilation.ofSource(MODEL.replace("OP", operator), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                compilation.db().ask(new Adequacy.Boundaries(MODULE)).value();
        assertNotNull(boundaries, () -> "the model under test compiles: " + operator);
        List<BorderAssessment> lines = boundaries.get("countOverThreshold");
        assertNotNull(lines, "the behavior has lines");
        return BorderAssessment.pointsOf(lines).stream()
                .filter(point -> point.role().againstTheLine())
                .filter(point -> point.owed() != null).toList();
    }

    private static List<String> owedFor(String operator) {
        return pointsFor(operator).stream()
                .map(point -> point.border().axis() + " " + point.role() + " " + point.against()
                        + " " + point.owed().coverage())
                .toList();
    }

    /** The line is at the element, and the points against it are values of the element. */
    @Test
    void thePointsAgainstTheLineAreValuesOfTheElement() {
        List<BorderAssessment.Point> points = pointsFor(">=");

        assertEquals(List.of("countOverThreshold/items[*].charge"),
                points.stream().map(point -> point.border().axis()).distinct().toList());
        assertEquals(List.of("21000", "20999"),
                points.stream().filter(point -> point.against() != null)
                        .map(BorderAssessment.Point::against).distinct().toList());
    }

    /**
     * And the rows leave the two spellings of the threshold saying different things.
     *
     * <p>The whole of what the issue reports. The rows are the same for both, and what is owed
     * against the line is not: an item charged exactly 21000 is on one side under {@code >=} and on
     * the other under {@code >}, and no row among these is at it.
     */
    @Test
    void theTwoSpellingsOfTheThresholdAreNotOneMeasurement() {
        assertNotEquals(owedFor(">="), owedFor(">"),
                () -> "rewriting the comparison moved the line: " + owedFor(">="));
    }

    /**
     * And the point at the threshold is one these rows were read against and do not reach.
     *
     * <p>Missed and not undecided. The rows write their items plainly and one of them writes none
     * at all, so what is owed here is a row an author can go and write — told that a value could
     * not be read, they would go looking for what is wrong with the rows they have.
     */
    @Test
    void thePointAtTheThresholdIsOwedAndMissed() {
        List<BorderAssessment.Point> at = pointsFor(">=").stream()
                .filter(point -> "21000".equals(point.against())).toList();

        assertEquals(1, at.size(), () -> "one point at the threshold: " + owedFor(">="));
        assertEquals(new ItemAssessment.Coverage.Missed(), at.get(0).owed().coverage(),
                "every row was read here, and none writes an item charged exactly 21000");
    }

    /**
     * And a row whose list holds an item at the threshold reaches it.
     *
     * <p>The other half, so that "missed" is not what this reports of every row. One element among
     * several standing at the point is the row standing there.
     */
    @Test
    void aRowHoldingAnItemAtTheThresholdReachesThePoint() {
        Compilation compilation = Compilation.ofSource(MODEL.replace("OP", ">=")
                .replace("Item { charge = 1000 }", "Item { charge = 21000 }"), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        List<BorderAssessment> lines = compilation.db().ask(new Adequacy.Boundaries(MODULE))
                .value().get("countOverThreshold");
        BorderAssessment.Point at = BorderAssessment.pointsOf(lines).stream()
                .filter(point -> point.role().againstTheLine()).filter(point -> point.owed() != null)
                .filter(point -> "21000".equals(point.against())).findFirst().orElseThrow();

        assertEquals(new ItemAssessment.Coverage.Hit(), at.owed().coverage(),
                "the row holds an item at the threshold, among others");
    }
}
