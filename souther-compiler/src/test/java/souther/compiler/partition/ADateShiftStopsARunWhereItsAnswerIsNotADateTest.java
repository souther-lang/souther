package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.PathReachability;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.reach.ComparisonArrival;
import souther.compiler.report.AdequacyReport;
import souther.compiler.types.ConstructOccurrence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
     * What the step is handed is the same values however they reach it: a list given a name, an
     * element given a name, and a step given a name are the list, the element and the step
     * written out.
     */
    @Test
    void aListAnElementAndAStepGivenANameStopTheRunAsTheyDoWrittenOut() {
        for (String moved : List.of(
                "let xs = [0, 1, 2]\n    let ys = List.map(k -> Date.addDays(k * n, d), xs)",
                "let one = 1\n    let ys = List.map(k -> Date.addDays(k * n, d), [0, one])",
                "let shift = k -> Date.addDays(k * n, d)\n    let ys = List.map(shift, [0, 1, 2])",
                "let shift = k -> Date.addDays(k * n, d)\n    let ys = List.map(shift, [0, 1, 2])"
                        + "\n    let zs = List.map(shift, [0])")) {
            String report = report("""
                        guard n == %s else No
                        %s
                        guard b > 3 else No""".formatted(GREATEST, moved));
            assertTrue(nothingArrivesAbout(report, "b"), moved + "\n" + report);
        }
    }

    /**
     * A step is applied under what holds where it is applied and not where it was written: the
     * guard that leaves no date past the shift comes after the step is given its name.
     */
    @Test
    void aStepWrittenBeforeWhatStopsItIsReadWhereItIsApplied() {
        String report = report("""
                    let shift = k -> Date.addDays(k * n, d)
                    guard n == %s else No
                    let ys = List.map(shift, [0, 1, 2])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
        String alone = report("""
                    let shift = k -> Date.addDays(n, d)
                    guard n == %s else No
                    let ys = List.map(shift, [0, 1, 2])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(alone, "b"), "a step reading no element\n" + alone);
    }

    /**
     * What a step may stop on is the step's, whatever may have stopped a run before it: a shift
     * worked out on the way to the call is of the same kind as the step's own, and the step's
     * still stops every run on the element that is the greatest count.
     */
    @Test
    void aStepStopsTheRunWhateverStoppedARunOfTheSameKindBeforeIt() {
        String report = report("""
                    let early = Date.addDays(size, d)
                    guard n == %s else No
                    let ys = List.map(k -> Date.addDays(k, d), [0, n])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
        String alone = report("""
                    guard n == %s else No
                    let ys = List.map(k -> Date.addDays(k, d), [0, n])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(alone, "b"), "nothing before the step\n" + alone);
    }

    /**
     * A step a walk carries a value through is handed the element and what the applications
     * before it made, and only the element is a value written out: what is carried is read as any
     * value it may be. Carried here, it stays nought, and the shift by it moves no date; the same
     * shift by the element stops every run.
     */
    @Test
    void whatAWalkCarriesIsNoElementOfTheList() {
        String carried = report("""
                    guard n == %s else No
                    let total = List.fold((acc, k) -> { let moved = Date.addDays(acc * n, d)
                        acc }, 0, [1, 2])
                    guard b > 3 else No""".formatted(GREATEST));
        assertFalse(nothingArrivesAbout(carried, "b"), carried);
        String element = report("""
                    guard n == %s else No
                    let total = List.fold((acc, k) -> { let moved = Date.addDays(k * n, d)
                        acc }, 0, [1, 2])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(element, "b"), element);
    }

    /**
     * An element handed on an application of another closure is the value that application
     * handed it: on the outer application to {@code 1}, the inner one is handed {@code 1} too.
     */
    @Test
    void anElementAnOuterApplicationHandsIsWhatItHandsOnThatApplication() {
        String report = report("""
                    guard n == %s else No
                    let ys = List.map(j -> List.map(k -> Date.addDays(k * n, d), [j]), [0, 1])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
    }

    /**
     * An element is read where the list was written, which need not be where the step is applied:
     * a list a helper makes of what it is handed holds that value under the helper's own name.
     */
    @Test
    void anElementIsReadWhereTheListHoldingItWasWritten() {
        Compilation compilation = Compilation.ofSource("""
                module w1
                let pair (x: Int): List<Int> = [0, x]
                behavior f : (n: Int, d: Date, b: Int, size: Int) -> Ok | No
                let f (n, d, b, size) = {
                    guard n == %s else No
                    let ys = List.map(k -> Date.addDays(k * n, d), pair(1))
                    guard b > 3 else No
                    Ok
                }
                """.formatted(GREATEST), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(nothingArrivesAbout(report, "b"), report);
    }

    /**
     * Each application is shown to stop on its own or not at all. Here the one on {@code 1} gets
     * past where {@code b} is below nought and the one on {@code -1} where it is not, so no run
     * gets past both — and that is not shown: the line after them stays drawn. Alone, the first
     * is shown to stop where {@code b} is not below nought.
     */
    @Test
    void aStopOnlyTheApplicationsTogetherLeaveIsNotShown() {
        assertFalse(nothingArrivesAbout(report("""
                    guard n == %s else No
                    let ys = List.map(k -> b + k * n + k, [1, -1])
                    guard size > 3 else No""".formatted(GREATEST)), "size"));
        assertTrue(nothingArrivesAbout(report("""
                    guard n == %s else No
                    guard b >= 0 else No
                    let ys = List.map(k -> b + k * n + k, [1])
                    guard size > 3 else No""".formatted(GREATEST)), "size"));
    }

    /**
     * A list another walk made is one the tree that runs holds as that walk's build, and no
     * reading writes the elements of a build out, so the applications over it are not walked and
     * the line after them stays drawn.
     */
    @Test
    void aListAnotherWalkMadeIsNotWrittenOutAndTheLineAfterItStays() {
        String report = report("""
                    guard n == %s else No
                    let xs = List.map(x -> x, [0, 1, 2])
                    let ys = List.map(k -> Date.addDays(k * n, d), xs)
                    guard b > 3 else No""".formatted(GREATEST));
        assertFalse(nothingArrivesAbout(report, "b"), report);
    }

    /**
     * A condition in the step is what the model's condition means, which says what it states on
     * each application without saying which application states which; a path takes in what must
     * hold, so a fork the handed value decides is not decided by these walks, and the line after
     * stays drawn.
     */
    @Test
    void aForkTheHandedValueDecidesIsNotDecidedOnTheApplication() {
        String report = report("""
                    guard n == %s else No
                    let ys = List.map(k -> if k > 0 then Date.addDays(n, d) else d, [0, 1])
                    guard b > 3 else No""".formatted(GREATEST));
        assertFalse(nothingArrivesAbout(report, "b"), report);
    }

    /** A filter hands its step every element as a map does, and a step that stops on one stops
     *  the run. */
    @Test
    void aFilterWhoseStepStopsOnAnElementStopsTheRun() {
        String report = report("""
                    guard n == %s else No
                    let kept = List.filter(k -> Date.addDays(k * n, d) == d, [0, 1, 2])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
    }

    @Test
    void aFilterWhoseStepStopsOnNoElementLeavesTheRunsAfterItOpen() {
        String report = report("""
                    guard n == 0 else No
                    let kept = List.filter(k -> Date.addDays(k * n, d) == d, [0, 1, 2])
                    guard b > 3 else No""");
        assertFalse(nothingArrivesAbout(report, "b"), report);
    }

    /**
     * An operation that stops at the first element its step holds of hands the later ones on no
     * run that stopped there: the step holds of {@code 0}, so the element it would stop on is not
     * one the run is handed.
     */
    @Test
    void aStepThatWouldStopOnAnElementAfterTheOneThatSettlesTheAnswerLeavesTheRunOpen() {
        String report = report("""
                    guard n == %s else No
                    let any = List.any(k -> Date.addDays(k * n, d) == d, [0, 1, 2])
                    guard b > 3 else No""".formatted(GREATEST));
        assertFalse(nothingArrivesAbout(report, "b"), report);
    }

    /**
     * An element the list holds on some runs is handed to the step on those runs only: where the
     * list is chosen empty, the step that stops on every element is applied to none and the run
     * goes on.
     */
    @Test
    void aStepAppliedToElementsSomeRunsHoldLeavesTheRunsThatHoldNoneOpen() {
        String report = report("""
                    guard n == %s else No
                    let moved = List.map(k -> Date.addDays(n, d), if size > 3 then [0, 1] else [])
                    guard b > 3 else No""".formatted(GREATEST));
        assertFalse(nothingArrivesAbout(report, "b"), report);
    }

    /** What the reading of where a run arrives answers about {@code body}, read whole: every
     *  comparison and arm, and not only those a line is drawn at. */
    private static PathReachability.Answers arrivals(String body) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior f : (n: Int, d: Date, b: Int, size: Int) -> Ok | No
                let f (n, d, b, size) = {
                %s
                    Ok
                }
                """.formatted(body), "Main");
        PathReachability.Answers answers = compilation.db().ask(new Adequacy.Arrived("w1"))
                .value().get("f").answers();
        assertFalse(answers.arrivals().arriving().isEmpty(), "the comparisons were read");
        return answers;
    }

    /** The comparisons {@code answers} says nothing arrives at. */
    private static List<ConstructOccurrence> nothingArrivesAt(PathReachability.Answers answers) {
        return answers.arrivals().arriving().entrySet().stream()
                .filter(each -> each.getValue() instanceof ComparisonArrival.NothingArrives)
                .map(Map.Entry::getKey).toList();
    }

    /**
     * The arguments of the call are worked out before it applies its step, whichever side of the
     * step they are written on: a comparison deciding an element is arrived at, and only what
     * follows the call is not. No line is drawn at the one deciding the element, so it is asked of
     * the reading, with nothing after the call: then no comparison is one nothing arrives at.
     */
    @Test
    void anElementWorkedOutBeforeTheApplicationsIsArrivedAtAndWhatFollowsThemIsNot() {
        String moved = """
                    guard n == %s else No
                    let moved = List.map(k -> Date.addDays(n, d), [0, if size > 3 then 1 else 2])"""
                .formatted(GREATEST);
        String report = report(moved + "\n    guard b > 3 else No");
        assertTrue(nothingArrivesAbout(report, "b"), report);
        assertEquals(List.of(), nothingArrivesAt(arrivals(moved)));
    }

    /**
     * A comparison in the step is one place for every application, and arrived at where any
     * application arrives at it: the one on {@code 0} gets to both comparisons in the step, though
     * the one on {@code 1} stops before either. Nothing follows the call here, so no comparison of
     * the body is one nothing arrives at, and no arm one nothing enters.
     */
    @Test
    void aComparisonInTheStepOneApplicationArrivesAtIsArrivedAt() {
        PathReachability.Answers answers = arrivals("""
                    guard n == %s else No
                    let seen = List.map(k -> if Date.addDays(k * n, d) == d
                        then (if size > 3 then 1 else 2) else 0, [0, 1, 2])""".formatted(GREATEST));
        assertEquals(List.of(), nothingArrivesAt(answers));
        assertFalse(answers.found().isEmpty(), "the arms were read");
        assertEquals(List.of(), answers.found().entrySet().stream()
                .filter(each -> each.getValue()
                        instanceof souther.compiler.reach.Reachability.Unreachable)
                .map(Map.Entry::getKey).toList());
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
