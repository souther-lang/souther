package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.RuleWhereARunMayStop;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A line through an element a walk hands its step, where the container is made of the input, is
 * drawn where the elements the way leaves put it, and nowhere a number the way leaves out would.
 *
 * <p>Asked of the lines as the rules alone draw them and of the rules a run may stop in, which are
 * the owners of both answers: where a line falls takes no row, and none is composed here.
 */
class ALineThroughAnElementIsDrawnWhereTheElementPutsItTest {

    /** {@code a + n >= 10} over {@code List.rangeInclusive(3, days)} is at {@code a} of seven,
     *  where the element is three. */
    @Test
    void aLineThroughAWholeNumberInTurnIsAtTheFirstElement() {
        assertEquals(List.of("7"), linesOn(compiled("a: Int, days: Int", "List<Int>",
                FROM_THREE)));
    }

    /**
     * {@code a + i >= 3} over where an element of {@code xs} stands is at {@code a} of three, where
     * the element stands first. And no line is drawn where the position meets the most a list
     * holds, which is the language's end and no model's.
     */
    @Test
    void aLineThroughWhereAnElementStandsIsAtTheFirstPlace() {
        assertEquals(List.of("3"), linesOn(compiled("a: Int, xs: List<Int>", "List<Bool>",
                "List.mapIndexed((i, _) -> a + i >= 3, xs)")));
    }

    /**
     * A way holding the last end at five or less leaves the element every number from three to
     * five and no other, so {@code a + n >= 10} is settled true from seven and false to four.
     */
    @Test
    void aWayBoundingTheLastEndDrawsALineAtTheMostTheElementTakes() {
        assertEquals(List.of("4", "7"), linesOn(compiled("a: Int, days: Int", "List<Int>",
                "if days <= 5 then " + FROM_THREE + " else []")));
    }

    /**
     * A way leaving out the last end's most and the one below it leaves the element three alone:
     * one line, and none where a number the way leaves out would have put one.
     */
    @Test
    void aNumberTheWayLeavesOutDrawsNoLine() {
        assertEquals(List.of("6"), linesOn(compiled("a: Int, days: Int", "List<Int>",
                "if days <= 5 then (if days == 5 then [] else (if days == 4 then [] else "
                        + FROM_THREE + ")) else []")));
    }

    /** A way on which the list holds nothing makes no application: no line through the element,
     *  and no run that may stop in the sum over it. */
    @Test
    void aWayOnWhichTheListHoldsNothingDrawsNothingThroughTheElement() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "if days < 3 then " + FROM_THREE + " else []");
        assertEquals(List.of(), linesOn(compilation));
        assertEquals(List.of(), mayStop(compilation));
    }

    /** Ends that move together are not shown to leave the element every number, so nothing is
     *  said of which values of {@code a} settle the comparison. */
    @Test
    void endsThatMoveTogetherShowNothingTheElementTakes() {
        assertEquals(List.of(), linesOn(compiled("a: Int, days: Int", "List<Int>",
                "List.rangeInclusive(days, days + 3) |> List.filter(n -> a + n >= 10)")));
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

    /** The rules of {@code m} some run reaching them may stop in. */
    private static List<RuleWhereARunMayStop> mayStop(Compilation compilation) {
        Partitions.Partitioning divided =
                compilation.db().ask(new Adequacy.Divided("w1", "m")).value();
        assertNotNull(divided, "m was divided");
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return divided.rulesWhereARunMayStop();
    }

    /** Where the lines of {@code m} on {@code a} are drawn, in the order they are read. */
    private static List<String> linesOn(Compilation compilation) {
        List<BorderAssessment> lines =
                compilation.db().ask(new Adequacy.Boundaries("w1", "m")).value();
        assertNotNull(lines, "m was read");
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return lines.stream().filter(line -> line.left().equals("a"))
                .map(BorderAssessment::value).toList();
    }

    private static Compilation compiled(String parameters, String answer, String body) {
        return Compilation.ofSource("""
                module w1
                behavior m : (%s) -> %s
                let m (%s) = %s
                """.formatted(parameters, answer, parameters.replaceAll(":\\s*[A-Za-z<>]+", ""),
                body), "Main");
    }
}
