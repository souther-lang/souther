package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison inside a closure, one side of which is a total over the elements a filter keeps,
 * has the ways the elements are kept in split once for all the applications of the closure when
 * the total is the same on each of them, and only the constant it is compared with differs. One
 * that turns on the application, in the filter or through a helper handed the application's value,
 * is another total on each and is split with all of them.
 */
class AComparisonInAClosureIsReadOnceForTheWaysOfATotalThatDoesNotTurnOnTheElementTest {

    private static final String PREAMBLE = """
            module p
            data Month = { pay: Int, days: Int }
            data Window = { first: Month, second: Month, third: Month, fourth: Month }
            data Ok
            data No
            """;

    /** The ways four months are each kept or dropped in. */
    private static final int WAYS = 16;

    /** How many constants walked against the total are more readings than one condition is read
     *  in, once for each way. */
    private static final int PAST_THE_READINGS =
            CompositionBudget.READINGS_OF_ONE_CONDITION.maximum() / WAYS + 1;

    private static final String MONTHS = "[ w.first, w.second, w.third, w.fourth ]";

    /** How many of the four months are kept. */
    private static final String KEPT = "List.length(List.filter(r -> r.days >= 17, " + MONTHS + "))";

    private static String report(String body) {
        Compilation compilation = Compilation.ofSource(PREAMBLE + body, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()))
                .replaceAll("\\d+:\\d+", "");
    }

    private static String table(int rows) {
        return IntStream.rangeClosed(1, rows).mapToObj(Integer::toString)
                .collect(Collectors.joining(", ", "[ ", " ]"));
    }

    /** {@code helpers} written before a behavior that asks whether some constant of a table of
     *  {@code rows} is at most {@code total}. */
    private static String walked(String helpers, String total, int rows) {
        return helpers + """
                behavior g : (w: Window) -> Ok | No
                let g (w) = {
                    guard List.any(t -> t <= %s, %s) else No
                    Ok
                }
                """.formatted(total, table(rows));
    }

    static String reachedBy(String total, int rows) {
        return report(walked("", total, rows));
    }

    @Test
    void aTableWalkedAgainstAFilteredTotalIsReadWhateverItsLength() {
        String report = reachedBy(KEPT, PAST_THE_READINGS);
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
        assertTrue(report.contains("read as g/w.first.days"), report);
    }

    /**
     * A table short enough to have been read before draws the lines it draws when it is longer
     * than the figure allows.
     */
    @Test
    void aLongTableDrawsTheLinesAShortOneDoes() {
        Set<String> drawnByTheLongTable = linesOn(reachedBy(KEPT, PAST_THE_READINGS));
        for (int shorter : new int[] {1, 2, 8}) {
            Set<String> drawn = linesOn(reachedBy(KEPT, shorter));
            assertFalse(drawn.isEmpty(), "rows " + shorter);
            Set<String> missing = new TreeSet<>(drawn);
            missing.removeAll(drawnByTheLongTable);
            assertEquals(Set.of(), missing, "rows " + shorter);
        }
    }

    private static Set<String> linesOn(String report) {
        return report.lines().filter(line -> line.contains("read as"))
                .map(line -> line.strip().replaceFirst(" — .*", ""))
                .collect(Collectors.toSet());
    }

    /** A filter that compares with the constant is another filter on each application. */
    @Test
    void aTotalWhoseFilterTurnsOnTheApplicationIsStillStoppedByTheFigure() {
        String report = reachedBy("List.sum(List.map(r -> r.pay,"
                + " List.filter(r -> r.days >= t, " + MONTHS + ")))", PAST_THE_READINGS);
        assertTrue(report.contains("READINGS_OF_ONE_CONDITION"), report);
    }

    /** Handed the constant through a helper, the dependence is the same one. */
    @Test
    void aTotalWhoseHelperIsHandedTheApplicationIsStillStoppedByTheFigure() {
        String helpers = """
                let keptFrom (t: Int, w: Window): Int =
                    List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= t, %s)))
                """.formatted(MONTHS);
        String report = report(walked(helpers, "keptFrom(t, w)", PAST_THE_READINGS));
        assertTrue(report.contains("READINGS_OF_ONE_CONDITION"), report);
    }

    /**
     * What is split is any value, and not only a total: a library operation defined by its cases
     * is split into them, and is the same cases on every application when nothing the application
     * was handed is among its arguments.
     */
    @Test
    void aLibraryOperationOverTheApplicationsValueIsSplitWithAllOfThem() {
        int rows = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum() / 2 + 1;
        String report = reachedBy("Int.max(w.first.pay, t)", rows);
        assertTrue(report.contains("READINGS_OF_ONE_CONDITION"), report);
    }

    /**
     * Sharing the readings of a value no application is handed does not share the lines they
     * draw: each application draws its own, and where all of them are on one quantity the stages
     * after the reading are held to what the readings were. Cases that are each another quantity
     * are not that many lines on any one.
     */
    @Test
    void manyLinesOnOneQuantityAreNotWorkedOutHoweverTheyCameBy() {
        int rows = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum() / 2 + 1;
        String report = reachedBy("Int.abs(w.first.pay)", rows);
        assertTrue(report.contains("READINGS_OF_ONE_CONDITION"), report);
    }

    /**
     * Applications of a closure inside another, with a value chosen by cases read beside them and
     * a value taken from a helper: the readings a split is counted among stay a whole number of
     * the applications on every path, which a reading that cannot say how many it is one of
     * refuses to be.
     */
    @Test
    void closuresInsideClosuresWithChoicesAndHelpersKeepTheCountOfApplicationsWhole() {
        String helpers = """
                let spread (w: Window): Int = Int.abs(w.first.pay - w.second.pay)
                let pick (w: Window, t: Int): Int = if w.third.pay > t then 1 else 0
                """;
        String report = report(helpers + """
                behavior g : (w: Window) -> Ok | No
                let g (w) = {
                    guard List.any(t -> List.any(s -> s <= t + spread(w) + pick(w, t), [ 1, 2, 3 ]),
                        %s) else No
                    Ok
                }
                """.formatted(table(6)));
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
    }

    /**
     * A value that turns on the outer closure's parameter only is split with the outer
     * applications, and not also with the inner closure's, which it is the same on: the readings
     * are the outer ones times its cases, however long the inner table.
     */
    @Test
    void aValueTurningOnTheOuterParameterAloneIsNotSplitWithTheInnerApplications() {
        int outer = 8;
        int inner = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum() / outer;
        String report = report("""
                behavior g : (w: Window) -> Ok | No
                let g (w) = {
                    guard List.any(t -> List.any(s -> s <= Int.max(t, w.first.pay), %s), %s) else No
                    Ok
                }
                """.formatted(table(inner), table(outer)));
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
    }

    private static String monthsRepeated(int times) {
        return IntStream.range(0, times).mapToObj(i -> "w.first")
                .collect(Collectors.joining(", ", "[ ", " ]"));
    }

    /** What the closure over the months reads of its parameter, said directly or through a name. */
    private static String readingTheParameter(String bound, String read, int months) {
        return report("""
                behavior g : (w: Window) -> Ok | No
                let g (w) = {
                    guard List.any(t -> {
                        %s
                        List.any(s -> s <= Int.max(%s, 0), [ 1 ])
                    }, %s) else No
                    Ok
                }
                """.formatted(bound, read, monthsRepeated(months)));
    }

    /**
     * A name given the parameter's field is the parameter's field: the cases of a value split are
     * as many as the values the parameter is handed whether it is said directly or through the
     * name, which is a position either way.
     */
    @Test
    void aNameGivenTheParametersFieldIsSplitWithTheParametersApplicationsAsTheFieldIs() {
        int months = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum() / 2 + 1;
        String direct = readingTheParameter("", "t.pay", months);
        assertTrue(direct.contains("READINGS_OF_ONE_CONDITION"), direct);
        String named = readingTheParameter("let x = t.pay", "x", months);
        assertTrue(named.contains("READINGS_OF_ONE_CONDITION"), named);
    }

    /** A helper that is handed nothing of the application is the same total on each. */
    @Test
    void aTotalFromAHelperHandedNothingOfTheApplicationIsReadWhateverTheTableLength() {
        String helpers = """
                let kept (w: Window): Int =
                    List.length(List.filter(r -> r.days >= 17, %s))
                """.formatted(MONTHS);
        String report = report(walked(helpers, "kept(w)", PAST_THE_READINGS));
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
        assertTrue(report.contains("read as g/w.first.days"), report);
    }
}
