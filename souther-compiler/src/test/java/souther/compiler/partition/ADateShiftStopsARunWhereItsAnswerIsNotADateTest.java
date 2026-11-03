package souther.compiler.partition;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run gets past a date moved by a count of days only where the date it comes to is one, and what
 * is worked out on the way to it is read the same wherever the count and the list it is applied
 * to come from.
 *
 * <p>Each holding is shown beside a control the same but for one value, where a run does get
 * there, so that a line dropped is a line dropped for this reason. A line is dropped only where no
 * run arrives at it; the controls are the ones that matter, since a run said to arrive where none
 * does is the safe error and a run said not to where one does is not.
 */
class ADateShiftStopsARunWhereItsAnswerIsNotADateTest {

    private static final String GREATEST = "9223372036854775807";

    private static String report(String body) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior f : (n: Int, d: Date, b: Int, size: Int) -> Ok | No
                let f (n, d, b, size) = {
                %s
                    Ok
                }
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Whether the report says the line about {@code about} was drawn at no comparison because
     *  nothing that arrives there holds a value at it. */
    private static boolean nothingArrivesAbout(String report, String about) {
        return report.lines().anyMatch(line -> line.contains("no line: comparison@")
                && line.contains("about `" + about + "`"));
    }

    /** Whether every point the report names at the comparison written at {@code at} is one it
     *  left undecided, and it names some: no row is said to be at one, nor none to arrive. */
    private static boolean everyPointIsLeftUndecidedAt(String report, String at) {
        List<String> points = report.lines().map(String::strip)
                .filter(line -> line.contains("point (comparison@" + at + ")"))
                .filter(line -> line.startsWith("?") || line.startsWith("!"))
                .toList();
        return !points.isEmpty() && points.stream().allMatch(line -> line.startsWith("?"));
    }

    @Test
    void aShiftByACountNoDateIsMovedByStopsTheRunsAfterIt() {
        String report = report("""
                    guard n == %s else No
                    let moved = Date.addDays(n, d)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
    }

    @Test
    void aShiftByACountADateIsMovedByLeavesTheRunsAfterItOpen() {
        String report = report("""
                    guard n == 0 else No
                    let moved = Date.addDays(n, d)
                    guard b > 3 else No""");
        assertFalse(nothingArrivesAbout(report, "b"), report);
    }

    /** A name is the value it was bound to, however long the chain of names to it. */
    @Test
    void aCountGivenANameStopsARunWhereTheCountWrittenOutDoes() {
        String report = report("""
                    guard n == %s else No
                    let once = n
                    let twice = once
                    let moved = Date.addDays(twice, d)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
    }

    @Test
    void aCountGivenANameLeavesTheRunsAfterItOpenWhereItIsNotStopped() {
        String report = report("""
                    guard n == 0 else No
                    let once = n
                    let twice = once
                    let moved = Date.addDays(twice, d)
                    guard b > 3 else No""");
        assertFalse(nothingArrivesAbout(report, "b"), report);
    }

    /**
     * The elements of a list are all made before the list is: a shift that stops on a later
     * element stops the run whatever an earlier one would have been found to be.
     */
    @Disabled("#3022: the reading of where nothing arrives reads a closure's body once, without the"
            + " value each application is handed, so a stop only some applications reach is not"
            + " placed")
    @Test
    void aShiftThatStopsOnALaterElementStopsTheRunThatWouldHaveFoundTheFirst() {
        String report = report("""
                    guard n == %s else No
                    let found = List.map(k -> Date.addDays(k * n, d), [0, 1, 2])
                        |> List.find(x -> x == d)
                        |> Option.withDefault(d)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
    }

    /**
     * Until then, the line after such a list is left undecided, and no more: that nothing arrives
     * is not shown, and neither is it said that a row does.
     */
    @Test
    void aShiftThatStopsOnALaterElementLeavesTheLineAfterItUndecided() {
        String report = report("""
                    guard n == %s else No
                    let found = List.map(k -> Date.addDays(k * n, d), [0, 1, 2])
                        |> List.find(x -> x == d)
                        |> Option.withDefault(d)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(everyPointIsLeftUndecidedAt(report, "8:9"), report);
    }

    @Test
    void aShiftThatStopsOnNoElementLeavesTheRunsAfterTheFindOpen() {
        String report = report("""
                    guard n == 0 else No
                    let found = List.map(k -> Date.addDays(k * n, d), [0, 1, 2])
                        |> List.find(x -> x == d)
                        |> Option.withDefault(d)
                    guard b > 3 else No""");
        assertFalse(nothingArrivesAbout(report, "b"), report);
    }

    /** A list whose ends are not written out is not shown to be made, so nothing is said of what
     *  stops it: the run is left to arrive. */
    @Test
    void aRangeWhoseEndIsAnInputIsNotShownToBeMade() {
        String report = report("""
                    guard size >= 0 else No
                    let found = List.rangeInclusive(0, size)
                        |> List.map(k -> Date.addDays(k, d))
                        |> List.find(x -> x == d)
                        |> Option.withDefault(d)
                    guard b > 3 else No""");
        assertFalse(nothingArrivesAbout(report, "b"), report);
    }

    @Disabled("#3022: the reading of where nothing arrives reads a closure's body once, without the"
            + " value each application is handed, so a stop only some applications reach is not"
            + " placed")
    @Test
    void aRangeWhoseEndsAreWrittenOutAndAShiftThatStopsOnItsElementsStopsTheRun() {
        String report = report("""
                    guard n == %s else No
                    let found = List.rangeInclusive(0, 2)
                        |> List.map(k -> Date.addDays(k * n, d))
                        |> List.find(x -> x == d)
                        |> Option.withDefault(d)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
    }

    @Test
    void aRangeWhoseEndsAreWrittenOutAndAShiftThatStopsOnItsElementsLeavesTheLineUndecided() {
        String report = report("""
                    guard n == %s else No
                    let found = List.rangeInclusive(0, 2)
                        |> List.map(k -> Date.addDays(k * n, d))
                        |> List.find(x -> x == d)
                        |> Option.withDefault(d)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(everyPointIsLeftUndecidedAt(report, "9:9"), report);
    }

    @Test
    void anEmptyRangeLeavesTheRunsAfterItOpen() {
        String report = report("""
                    guard n == %s else No
                    let found = List.rangeInclusive(2, 0)
                        |> List.map(k -> Date.addDays(k * n, d))
                        |> List.find(x -> x == d)
                        |> Option.withDefault(d)
                    guard b > 3 else No""".formatted(GREATEST));
        assertFalse(nothingArrivesAbout(report, "b"), report);
    }
}
