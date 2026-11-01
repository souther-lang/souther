package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line through an element a walk hands its step, where the container is made of the input, is
 * measured by rows whose container holds that element: a row with nothing to walk never gets to
 * the comparison, whatever it holds at the line.
 *
 * <p>Held to the rows as they ran and were read back, and not to the conditions the way carries:
 * a row composed for the line that does not hold the element shows nothing of it.
 */
class ALineThroughAnElementIsMeasuredByRowsThatHoldTheElementTest {

    /**
     * {@code a + n >= 10} over {@code List.rangeInclusive(3, days)} is at {@code a} of seven, where
     * the element is three; a row at it, beside it or either side of it makes the list hold three,
     * which is {@code days} of three or more.
     */
    @Test
    void aLineThroughAWholeNumberInTurnIsMeasuredByRowsWhoseListHoldsIt() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>", FROM_THREE);
        assertEquals(List.of("7"), linesOn(compilation, "a"));
        List<ObservedInputs> rows = rowsAtEveryItem(compilation, "a");
        assertFalse(rows.isEmpty(), "the line has its rows");
        assertRowsHold(rows, 1, value -> value instanceof ObservedValue.Integer(long days)
                && days >= 3);
    }

    /**
     * {@code a + i >= 3} over where an element of {@code xs} stands is at {@code a} of three, where
     * the element stands first; a row there holds an element. And no line is drawn where the
     * position meets the most a list holds, which is the language's end and no model's.
     */
    @Test
    void aLineThroughWhereAnElementStandsIsMeasuredByRowsThatHoldAnElement() {
        Compilation compilation = compiled("a: Int, xs: List<Int>", "List<Bool>",
                "List.mapIndexed((i, _) -> a + i >= 3, xs)");
        assertEquals(List.of("3"), linesOn(compilation, "a"));
        List<ObservedInputs> rows = rowsAtEveryItem(compilation, "a");
        assertFalse(rows.isEmpty(), "the line has its rows");
        assertRowsHold(rows, 1, value -> value instanceof ObservedValue.Sequence(var elements)
                && !elements.isEmpty());
    }

    /**
     * A way holding the last end at five or less leaves the element every number from three to
     * five and no other, so {@code a + n >= 10} is settled true from seven and false to four; rows
     * at both lines make a list holding the element there.
     */
    @Test
    void aWayBoundingTheLastEndDrawsALineAtTheMostTheElementTakes() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "if days <= 5 then " + FROM_THREE + " else []");
        assertEquals(List.of("4", "7"), linesOn(compilation, "a"));
        assertRowsHold(rowsAtEveryItem(compilation, "a"), 1, value ->
                value instanceof ObservedValue.Integer(long days) && days >= 3 && days <= 5);
    }

    /**
     * A way leaving out the last end's most and the one below it leaves the element three alone:
     * one line, and none where a number the way leaves out would have put one.
     */
    @Test
    void aNumberTheWayLeavesOutDrawsNoLine() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "if days <= 5 then (if days == 5 then [] else (if days == 4 then [] else "
                        + FROM_THREE + ")) else []");
        assertEquals(List.of("6"), linesOn(compilation, "a"));
        assertRowsHold(rowsAtEveryItem(compilation, "a"), 1, value ->
                value instanceof ObservedValue.Integer(long days) && days == 3);
    }

    /** A way on which the list holds nothing makes no application: no line through the element,
     *  and no run that may stop in the sum over it. */
    @Test
    void aWayOnWhichTheListHoldsNothingDrawsNothingThroughTheElement() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "if days < 3 then " + FROM_THREE + " else []");
        assertEquals(List.of(), linesOn(compilation, "a"));
        assertEquals(List.of(), report(compilation).stream()
                .filter(line -> line.startsWith("· may stop")).toList());
    }

    /** Ends that move together are not shown to leave the element every number, so nothing is
     *  said of which values of {@code a} settle the comparison. */
    @Test
    void endsThatMoveTogetherShowNothingTheElementTakes() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "List.rangeInclusive(days, days + 3) |> List.filter(n -> a + n >= 10)");
        assertEquals(List.of(), linesOn(compilation, "a"));
    }

    /**
     * Where an element stands is kept below the most a list holds in what an operation over it
     * is shown to come to, along a way stating the list holds something as without one: one
     * added to it stops no run, and {@code a} added to it may.
     */
    @Test
    void theMostAListHoldsStillKeepsAnOperationOverWhereAnElementStands() {
        String holding = "if List.length(xs) >= 1 then List.mapIndexed((i, _) -> %s, xs) else []";
        assertEquals(List.of(), mayStop(compiled("a: Int, xs: List<Int>", "List<Bool>",
                holding.formatted("i + 1 == a"))));
        assertEquals(1, mayStop(compiled("a: Int, xs: List<Int>", "List<Bool>",
                holding.formatted("a + i >= 3"))).size());
    }

    private static final String FROM_THREE =
            "List.rangeInclusive(3, days) |> List.filter(n -> a + n >= 10)";

    private static List<String> mayStop(Compilation compilation) {
        return report(compilation).stream().filter(line -> line.startsWith("· may stop"))
                .toList();
    }

    private static List<String> report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).toList();
    }

    private static void assertRowsHold(List<ObservedInputs> rows, int parameter,
                                       Predicate<ObservedValue> holding) {
        for (ObservedInputs row : rows) {
            assertTrue(holding.test(row.inputs().get(parameter)), row::toString);
        }
    }

    /** The rows read back at every item owed of every line of {@code m} on {@code quantity}, every
     *  item owed having some. */
    private static List<ObservedInputs> rowsAtEveryItem(Compilation compilation, String quantity) {
        List<ObservedInputs> rows = new ArrayList<>();
        for (BorderAssessment line : measured(compilation)) {
            if (!line.left().equals(quantity)) {
                continue;
            }
            line.items().forEach((point, item) -> {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    return;
                }
                List<ObservedInputs> here = owed.searches().each().stream()
                        .filter(ItemAssessment.Attempt.Certified.class::isInstance)
                        .map(ItemAssessment.Attempt.Certified.class::cast)
                        .map(ItemAssessment.Attempt.Certified::readBack).toList();
                assertFalse(here.isEmpty(), () -> point + " has a row: " + owed);
                rows.addAll(here);
            });
        }
        return rows;
    }

    /** Where the lines of {@code m} on {@code quantity} are drawn, in the order they are
     *  measured. */
    private static List<String> linesOn(Compilation compilation, String quantity) {
        return measured(compilation).stream().filter(line -> line.left().equals(quantity))
                .map(BorderAssessment::value).toList();
    }

    private static List<BorderAssessment> measured(Compilation compilation) {
        List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), "w1").get("m");
        assertNotNull(lines, "m was measured");
        return lines;
    }

    private static Compilation compiled(String parameters, String answer, String body) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior m : (%s) -> %s
                let m (%s) = %s
                """.formatted(parameters, answer, parameters.replaceAll(":\\s*[A-Za-z<>]+", ""),
                body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return compilation;
    }
}
