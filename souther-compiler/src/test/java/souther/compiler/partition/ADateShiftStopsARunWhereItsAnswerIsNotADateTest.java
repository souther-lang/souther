package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.check.PathReachability;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.LabeledRegion;
import souther.compiler.diag.Note;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceRendering;
import souther.compiler.diag.msg.DeadBranchMessage;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.reach.ComparisonArrival;
import souther.compiler.report.AdequacyReport;
import souther.compiler.types.ConstructOccurrence;

import java.util.ArrayList;
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
        return reportOf("""
                module w1
                behavior f : (n: Int, d: Date, b: Int, size: Int) -> Ok | No
                let f (n, d, b, size) = {
                %s
                    Ok
                }
                """.formatted(body));
    }

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
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

    /** Whether the report says a run arrives at the comparison about {@code about}: a line is
     *  drawn there, so the comparison was read and is not one said to be out of reach. */
    private static boolean aRunArrivesAbout(String report, String about) {
        return !nothingArrivesAbout(report, about)
                && report.lines().anyMatch(line -> line.contains("read as f/" + about + ":"));
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
        assertTrue(aRunArrivesAbout(report, "b"), report);
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
        assertTrue(aRunArrivesAbout(report, "b"), report);
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
        assertTrue(aRunArrivesAbout(carried, "b"), carried);
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
        String report = reportOf("""
                module w1
                let pair (x: Int): List<Int> = [0, x]
                behavior f : (n: Int, d: Date, b: Int, size: Int) -> Ok | No
                let f (n, d, b, size) = {
                    guard n == %s else No
                    let ys = List.map(k -> Date.addDays(k * n, d), pair(1))
                    guard b > 3 else No
                    Ok
                }
                """.formatted(GREATEST));
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
        String report = report("""
                    guard n == %s else No
                    let ys = List.map(k -> b + k * n + k, [1, -1])
                    guard size > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(report, "size"), report);
        assertTrue(nothingArrivesAbout(report("""
                    guard n == %s else No
                    guard b >= 0 else No
                    let ys = List.map(k -> b + k * n + k, [1])
                    guard size > 3 else No""".formatted(GREATEST)), "size"));
    }

    /**
     * A list another walk made is written out as the list the operation that made it answers, each
     * element the step's answer on the element it was handed: the application to {@code 1} stops
     * here as it does where {@code xs} is written {@code [0, 1, 2]}. Beside it, a walk making
     * {@code 0} of every element hands the next one nothing it stops on.
     */
    @Test
    void aListAnotherWalkMadeIsWrittenOutAndTheLineAfterItIsDropped() {
        String report = report("""
                    guard n == %s else No
                    let xs = List.map(x -> x, [0, 1, 2])
                    let ys = List.map(k -> Date.addDays(k * n, d), xs)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
        String control = report("""
                    guard n == %s else No
                    let xs = List.map(x -> 0, [0, 1, 2])
                    let ys = List.map(k -> Date.addDays(k * n, d), xs)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(control, "b"), control);
    }

    /**
     * A closure given a name before it is handed over builds the list the one written there does,
     * and two walks handed it build each the list of what that walk was handed.
     */
    @Test
    void aWalkWhoseClosureWasNamedIsWrittenOutAsOneWrittenInPlace() {
        String body = """
                    guard n == %s else No
                    let same = (x) -> x
                    let zeros = List.map(same, [0, 0])
                    let ones = List.map(same, [0, 1])
                    let ys = List.map(k -> Date.addDays(k * n, d), %s)
                    guard b > 3 else No""";
        String fromOnes = report(body.formatted(GREATEST, "ones"));
        assertTrue(nothingArrivesAbout(fromOnes, "b"), fromOnes);
        String fromZeros = report(body.formatted(GREATEST, "zeros"));
        assertTrue(aRunArrivesAbout(fromZeros, "b"), fromZeros);
    }

    /**
     * What a closure reads beside its element is read where the closure was written: a named one
     * reading a binding before it, and one a helper writes reading the helper's parameter. Each
     * beside the same with the value it reads one less, where the list holds only {@code 0}.
     */
    @Test
    void whatAClosureReadsBesideItsElementIsReadWhereTheClosureWasWritten() {
        String named = """
                    guard n == %s else No
                    let offset = %s
                    let shift = (x) -> x + offset
                    let xs = List.map(shift, [0, 0])
                    let ys = List.map(k -> Date.addDays(k * n, d), xs)
                    guard b > 3 else No""";
        String shifted = report(named.formatted(GREATEST, "1"));
        assertTrue(nothingArrivesAbout(shifted, "b"), shifted);
        String unshifted = report(named.formatted(GREATEST, "0"));
        assertTrue(aRunArrivesAbout(unshifted, "b"), unshifted);
        String helper = """
                module w1
                let shifted (xs: List<Int>, by: Int): List<Int> = List.map(x -> x + by, xs)
                behavior f : (n: Int, d: Date, b: Int, size: Int) -> Ok | No
                let f (n, d, b, size) = {
                    guard n == %s else No
                    let ys = List.map(k -> Date.addDays(k * n, d), shifted([0, 0], %s))
                    guard b > 3 else No
                    Ok
                }
                """;
        String byOne = reportOf(helper.formatted(GREATEST, "1"));
        assertTrue(nothingArrivesAbout(byOne, "b"), byOne);
        String byNone = reportOf(helper.formatted(GREATEST, "0"));
        assertTrue(aRunArrivesAbout(byNone, "b"), byNone);
    }

    /** A filter's list holds the elements its step held of, and none it did not. */
    @Test
    void aListAFilterMadeHoldsWhatItsStepHeldOf() {
        String report = report("""
                    guard n == %s else No
                    let xs = List.filter(x -> x >= 0, [0, 1, 2])
                    let ys = List.map(k -> Date.addDays(k * n, d), xs)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
        String control = report("""
                    guard n == %s else No
                    let xs = List.filter(x -> x > 5, [0, 1, 2])
                    let ys = List.map(k -> Date.addDays(k * n, d), xs)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(control, "b"), control);
    }

    /**
     * An element a filter keeps on some runs only is handed to the next step on those runs only:
     * where {@code b} is past {@code 2} the list holds none, and the step that stops on every
     * element is applied to none.
     */
    @Test
    void anElementAFilterKeepsOnSomeRunsLeavesTheRunsThatKeepNoneOpen() {
        String report = report("""
                    guard n == %s else No
                    let xs = List.filter(x -> x > b, [0, 1, 2])
                    let ys = List.map(k -> Date.addDays(n, d), xs)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(report, "b"), report);
    }

    /** Each element of a chain of builds is read where each step was handed it. */
    @Test
    void aChainOfTwoBuildsIsWrittenOut() {
        String report = report("""
                    guard n == %s else No
                    let xs = List.map(x -> x, [0, 1, 2])
                    let kept = List.filter(x -> x >= 0, xs)
                    let ys = List.map(k -> Date.addDays(k * n, d), kept)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
        String control = report("""
                    guard n == %s else No
                    let xs = List.map(x -> x - x, [0, 1, 2])
                    let kept = List.filter(x -> x >= 0, xs)
                    let ys = List.map(k -> Date.addDays(k * n, d), kept)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(control, "b"), control);
    }

    /** A flatMap's list holds every element of each list its step answered. */
    @Test
    void aListAFlatMapMadeHoldsWhatEachStepAnswered() {
        String report = report("""
                    guard n == %s else No
                    let xs = List.flatMap(x -> [0, x], [2])
                    let ys = List.map(k -> Date.addDays(k * n, d), xs)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
        String control = report("""
                    guard n == %s else No
                    let xs = List.flatMap(x -> [0, 0], [2])
                    let ys = List.map(k -> Date.addDays(k * n, d), xs)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(control, "b"), control);
    }

    /**
     * Two walks over one list are two lists: the one the next step is handed is the one that made
     * {@code 0} of every element, and the other is not read in its place.
     */
    @Test
    void twoWalksOverOneListAreTwoLists() {
        String report = report("""
                    guard n == %s else No
                    let xs = [0, 1, 2]
                    let zeros = List.map(x -> 0, xs)
                    let same = List.map(x -> x, xs)
                    let ys = List.map(k -> Date.addDays(k * n, d), zeros)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(report, "b"), report);
        String other = report("""
                    guard n == %s else No
                    let xs = [0, 1, 2]
                    let zeros = List.map(x -> 0, xs)
                    let same = List.map(x -> x, xs)
                    let ys = List.map(k -> Date.addDays(k * n, d), same)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(other, "b"), other);
    }

    /**
     * A helper whose body is a walk is copied where each call stands, and each copy's list is the
     * one that copy was handed: the list made of {@code [0, 0]} holds nothing a step stops on, and
     * the one made of {@code [0, 1]} does.
     */
    @Test
    void eachCopyOfAHelperBuildsTheListItWasHanded() {
        String body = """
                module w1
                let same (xs: List<Int>): List<Int> = List.map(x -> x, xs)
                behavior f : (n: Int, d: Date, b: Int, size: Int) -> Ok | No
                let f (n, d, b, size) = {
                    guard n == %s else No
                    let zeros = same([0, 0])
                    let ones = same([0, 1])
                    let ys = List.map(k -> Date.addDays(k * n, d), %s)
                    guard b > 3 else No
                    Ok
                }
                """;
        String fromZeros = reportOf(body.formatted(GREATEST, "zeros"));
        assertTrue(aRunArrivesAbout(fromZeros, "b"), fromZeros);
        String fromOnes = reportOf(body.formatted(GREATEST, "ones"));
        assertTrue(nothingArrivesAbout(fromOnes, "b"), fromOnes);
    }

    /**
     * A list a fold the author wrote built is one nothing proved what it holds, even where it is
     * built the way a map's is: what the walk answers is not read off its step, and the line after
     * stays drawn.
     */
    @Test
    void aListAFoldTheAuthorWroteBuiltIsNotWrittenOut() {
        String report = report("""
                    guard n == %s else No
                    let xs = List.fold((acc, x) -> acc ++ [x], [], [0, 1, 2])
                    let ys = List.map(k -> Date.addDays(k * n, d), xs)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(report, "b"), report);
    }

    /**
     * A condition in the step states, on each application, what it states on that one: on the
     * application to {@code 1} the arm that shifts {@code d} by {@code n} is taken, and every run
     * stops there, whichever element comes first.
     */
    @Test
    void aForkTheHandedValueDecidesIsDecidedOnTheApplication() {
        String report = report("""
                    guard n == %s else No
                    let ys = List.map(k -> if k > 0 then Date.addDays(n, d) else d, [0, 1])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
        String turned = report("""
                    guard n == %s else No
                    let ys = List.map(k -> if k > 0 then Date.addDays(n, d) else d, [1, 0])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(turned, "b"), turned);
    }

    /** The same fork, where no application takes the arm that stops: each takes its own
     *  statement, and the line after stays drawn. */
    @Test
    void aForkNoApplicationTakesTheStoppingArmOfLeavesTheRunOpen() {
        String report = report("""
                    guard n == %s else No
                    let ys = List.map(k -> if k > 0 then Date.addDays(n, d) else d, [0, -1])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(report, "b"), report);
    }

    /**
     * What an application states is taken on that application and no other: the arm that shifts by
     * {@code (k - 1) * n} is taken on {@code 1}, where it shifts by none, and the arm taken on
     * {@code 0} shifts nothing. Taken on {@code 0}, the first would stop every run.
     */
    @Test
    void aStatementIsTakenOnTheApplicationThatStatesItAndNoOther() {
        String report = report("""
                    guard n == %s else No
                    let ys = List.map(k -> if k > 0 then Date.addDays((k - 1) * n, d) else d,
                        [1, 0])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(report, "b"), report);
    }

    /** A condition that reads nothing handed states one thing on every application, and is read
     *  as that one statement. */
    @Test
    void aForkEveryApplicationStatesAlikeIsReadAsOneStatement() {
        String report = report("""
                    guard n == %s else No
                    let ys = List.map(k -> if n > 0 then Date.addDays(n, d) else d, [0, 1])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
    }

    /**
     * Two copies of a helper's closure are two closures, each with applications of its own: the
     * copy over {@code [0, 0]} takes the shifting arm on none and the one over {@code [0, 1]} on
     * its second, and that one is taken for no application of the other.
     */
    @Test
    void eachCopyOfAHelpersClosureIsDecidedOnItsOwnApplications() {
        String report = reportOf("""
                module w1
                let shifted (xs: List<Int>, n: Int, d: Date): List<Date> =
                    List.map(k -> if k > 0 then Date.addDays(n, d) else d, xs)
                behavior f : (n: Int, d: Date, b: Int, size: Int) -> Ok | No
                let f (n, d, b, size) = {
                    guard n == %s else No
                    let xs = shifted([0, 0], n, d)
                    guard size > 3 else No
                    let ys = shifted([0, 1], n, d)
                    guard b > 3 else No
                    Ok
                }
                """.formatted(GREATEST));
        assertTrue(aRunArrivesAbout(report, "size"), report);
        assertTrue(nothingArrivesAbout(report, "b"), report);
    }

    /** A closure inside a closure is decided on the application of each it stands on. */
    @Test
    void aForkInsideAClosureInsideAClosureIsDecidedOnTheApplicationsOfBoth() {
        String report = report("""
                    guard n == %s else No
                    let ys = List.map(j -> List.map(k -> if k > j then Date.addDays(n, d) else d,
                        [0, 1]), [0])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
    }

    /**
     * The inner closure is one construct on both outer applications and states different things
     * on each: on the outer application to {@code 1} no inner one takes the arm, and on the one to
     * {@code 0} the one that does shifts by none. What one outer application states, taken on the
     * other, would stop every run.
     */
    @Test
    void anInnerClosureIsDecidedOnTheOuterApplicationItStandsOn() {
        String report = report("""
                    guard n == %s else No
                    let ys = List.map(j -> List.map(k -> if k > j
                        then Date.addDays((k - j - 1) * n, d) else d, [0, 1]), [0, 1])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(report, "b"), report);
    }

    /**
     * An element a filter drops on every run is handed to nothing, and the applications over what
     * it keeps are of what it keeps: the one handed {@code 1} shifts by none and the one handed
     * {@code 2} takes the other arm. Each element's statement taken on the element beside it would
     * shift by {@code n} on the second.
     */
    @Test
    void theApplicationsOverWhatAFilterKeepsAreOfTheElementsItKeeps() {
        String report = report("""
                    guard n == %s else No
                    let xs = List.filter(x -> x > 0, [0, 1, 2])
                    let ys = List.map(k -> if k > 1 then d else Date.addDays((k - 1) * n, d), xs)
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(report, "b"), report);
    }

    /**
     * An operation that applies its closure twice to each element hands each application the
     * element it hands it: on the element {@code 1} both take the arm that shifts by {@code n}, and
     * a run stops there; where no element takes it, none does.
     */
    @Test
    void aClosureAppliedTwiceToAnElementStatesOnBothWhatItStatesOnTheElement() {
        String report = report("""
                    guard n == %s else No
                    let ys = List.distinctBy(k -> if k > 0 then Date.addDays(n, d) else d, [0, 1])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAbout(report, "b"), report);
        String control = report("""
                    guard n == %s else No
                    let ys = List.distinctBy(k -> if k > 0 then Date.addDays(n, d) else d, [0, -1])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(control, "b"), control);
    }

    /**
     * A right fold hands its step the elements last first: the step handed {@code 1} shifts by
     * none and the one handed {@code 0} shifts nothing. Each element's statement taken on the
     * other would shift by {@code -n}.
     */
    @Test
    void aRightFoldIsDecidedOnTheElementEachApplicationIsHanded() {
        String report = report("""
                    guard n == %s else No
                    let c = List.foldRight((x, acc) -> if x > 0
                        then Date.addDays((x - 1) * n, acc) else acc, d, [1, 0])
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(aRunArrivesAbout(report, "b"), report);
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
        assertTrue(aRunArrivesAbout(report, "b"), report);
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
        assertTrue(aRunArrivesAbout(report, "b"), report);
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
        assertTrue(aRunArrivesAbout(report, "b"), report);
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
        assertTrue(aRunArrivesAbout(report, "b"), report);
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
        assertTrue(aRunArrivesAbout(report, "b"), report);
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
        assertTrue(aRunArrivesAbout(report, "b"), report);
    }

    /** The marks a dead branch after two calls of {@code shift} makes at a call of it, in the
     *  order {@code first} and {@code second} are written. */
    private static List<SourcePos> callsMarkedWhen(String first, String second) {
        List<Diagnostic> dead = Compiler.compileWithWarnings("""
                module w1

                data Ok
                data No
                data Answer = Ok | No

                let shift (x: Int, d: Date): Date = Date.addDays(x, d)

                behavior f : (n: Int, d: Date, b: Int) -> Answer
                let f (n, d, b) = {
                    guard n == %s else No
                    let early = %s
                    let late = %s
                    if b > 3 then Ok else No
                }
                """.formatted(GREATEST, first, second)).warnings().stream()
                .filter(each -> each.code().equals("E1327")).toList();
        assertFalse(dead.isEmpty());
        List<SourcePos> marked = new ArrayList<>();
        for (Diagnostic one : dead) {
            for (LabeledRegion each : one.secondary()) {
                if (each.said() instanceof DeadBranchMessage.ThisCallMadeTheCopyTheProofIsAbout made
                        && each.place() instanceof DiagnosticPlace.InSource there) {
                    assertEquals("shift", made.called());
                    marked.add(there.region().start());
                }
            }
        }
        return marked;
    }

    /**
     * A decision made inside a helper is marked at the call whose copy it was made in, so that two
     * calls of one helper are two marks, one at each call. Where the first call is the one that
     * cannot answer, no run gets to the second, so the second is not a step on the way and only the
     * first is marked.
     */
    @Test
    void aDecisionInAHelperIsMarkedAtTheCallItsCopyWasMadeAt() {
        List<SourcePos> marked = callsMarkedWhen("shift(0, d)", "shift(n, d)").stream()
                .distinct().sorted(SourcePos.IN_WRITTEN_ORDER).toList();
        assertEquals(2, marked.size(), marked.toString());
        List<SourcePos> swapped = callsMarkedWhen("shift(n, d)", "shift(0, d)").stream()
                .distinct().sorted(SourcePos.IN_WRITTEN_ORDER).toList();
        assertEquals(List.of(marked.getFirst()), swapped);
    }

    /** A date moved where it is written is in no copy of a helper, so no call is marked. */
    @Test
    void aDecisionOutsideAHelperIsMarkedAtNoCall() {
        assertEquals(List.of(), callsMarkedWhen("Date.addDays(0, d)", "Date.addDays(n, d)"));
    }

    /** The reports that nothing reaches an arm of {@code body}. */
    private static List<Diagnostic> deadBranches(String body) {
        return Compiler.compileWithWarnings("""
                module w1

                data Ok
                data No
                data Answer = Ok | No

                behavior f : (n: Int, d: Date, b: Int) -> Answer
                let f (n, d, b) = {
                %s
                    if b > 3 then Ok else No
                }
                """.formatted(body)).warnings().stream()
                .filter(each -> each.code().equals("E1327")).toList();
    }

    /**
     * Why no run gets past the call is said as the application no run gets past, the element it
     * is handed among what it says: what it marks inside the step holds on the application to
     * another element, and the first element is not the one nothing gets past. A shift written
     * outside a step is said as the way here alone.
     */
    @Test
    void whyNoRunGetsPastTheCallIsSaidAsTheApplicationNoRunGetsPast() {
        for (Map.Entry<String, Integer> each : Map.of("[0, 1, 2]", 1, "[0, 0, 1]", 2)
                .entrySet()) {
            List<Diagnostic> dead = deadBranches("""
                        guard n == %s else No
                        let ys = List.map(k -> Date.addDays(k * n, d), %s)"""
                    .formatted(GREATEST, each.getKey()));
            assertFalse(dead.isEmpty(), each.getKey());
            for (Diagnostic one : dead) {
                assertEquals(List.of(new DeadBranchMessage.NoRunGetsPastOneOfItsApplications(
                                each.getValue())),
                        one.notes().stream().map(Note::said).filter(
                                DeadBranchMessage.NoRunGetsPastOneOfItsApplications.class::isInstance)
                                .toList(), each.getKey());
                assertTrue(one.secondary().stream().map(LabeledRegion::said).anyMatch(
                        DeadBranchMessage.ThisAppliesAFunctionToEveryElement.class::isInstance),
                        each.getKey());
            }
        }
        List<Diagnostic> outside = deadBranches("""
                    guard n == %s else No
                    let moved = Date.addDays(n, d)""".formatted(GREATEST));
        assertFalse(outside.isEmpty());
        for (Diagnostic one : outside) {
            assertTrue(one.notes().stream().map(Note::said).noneMatch(
                    DeadBranchMessage.NoRunGetsPastOneOfItsApplications.class::isInstance));
        }
    }
}
