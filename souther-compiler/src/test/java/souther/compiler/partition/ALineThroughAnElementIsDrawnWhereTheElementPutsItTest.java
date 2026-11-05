package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A line through an element a walk hands its step, where the container is made of the input, is
 * drawn where the elements the way leaves put it, and nowhere a number the way leaves out would.
 *
 * <p>Each of these lines is read as no place of the author's line, so it owes no row and none is
 * searched for at it ({@link souther.compiler.query.SearchOutcomes#unneeded}); what is held here
 * is where the lines are.
 */
class ALineThroughAnElementIsDrawnWhereTheElementPutsItTest {

    /** {@code a + n >= 10} over {@code List.rangeInclusive(3, days)} is at {@code a} of seven,
     *  where the element is three. */
    @Test
    void aLineThroughAWholeNumberInTurnIsAtTheFirstElement() {
        assertEquals(List.of("7"), linesOn(compiled("a: Int, days: Int", "List<Int>", FROM_THREE),
                "a"));
    }

    /**
     * {@code a + i >= 3} over where an element of {@code xs} stands is at {@code a} of three, where
     * the element stands first. And no line is drawn where the position meets the most a list
     * holds, which is the language's end and no model's.
     */
    @Test
    void aLineThroughWhereAnElementStandsIsAtTheFirstPlace() {
        assertEquals(List.of("3"), linesOn(compiled("a: Int, xs: List<Int>", "List<Bool>",
                "List.mapIndexed((i, _) -> a + i >= 3, xs)"), "a"));
    }

    /**
     * A way holding the last end at five or less leaves the element every number from three to
     * five and no other, so {@code a + n >= 10} is settled true from seven and false to four.
     */
    @Test
    void aWayBoundingTheLastEndDrawsALineAtTheMostTheElementTakes() {
        assertEquals(List.of("4", "7"), linesOn(compiled("a: Int, days: Int", "List<Int>",
                "if days <= 5 then " + FROM_THREE + " else []"), "a"));
    }

    /**
     * A way leaving out the last end's most and the one below it leaves the element three alone:
     * one line, and none where a number the way leaves out would have put one.
     */
    @Test
    void aNumberTheWayLeavesOutDrawsNoLine() {
        assertEquals(List.of("6"), linesOn(compiled("a: Int, days: Int", "List<Int>",
                "if days <= 5 then (if days == 5 then [] else (if days == 4 then [] else "
                        + FROM_THREE + ")) else []"), "a"));
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
