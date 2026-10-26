package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The year, the month or the day of a date moved by some days is a number of its own, not the
 * number of the date it was moved from.
 *
 * <p>The year of 31 December and the year of the next day differ, so a guard that holds of the
 * first and fails of the second is reachable, and the arm behind it is owed a row. Naming the two
 * as one number would make the guard contradict itself, find the arm unreachable, and drop a row
 * that is owed: an arm the report no longer asks for, and no longer a coverage obligation
 * anyone sees.
 */
class ThePartOfAShiftedDateIsNotThePartOfTheDateTest {

    private static final String OWED = "no row goes through `else`";

    private static String report(String guard) {
        return report(guard, LocalDate.of(2026, 6, 15));
    }

    /** The report of a behavior guarded by {@code guard}, with one row at {@code day}, which is a
     *  date the guard is expected to hold of. */
    private static String report(String guard, LocalDate day) {
        Compilation compilation = Compilation.ofSource("""
                module m

                data Yes = { v: Int }
                data No = { why: Int }

                behavior f : (d: Date) -> Yes | No
                    constructs Yes
                    constructs No

                let f (d) = {
                    guard %s else No { why = 1 }
                    Yes { v = 1 }
                }

                example f
                    | "r" : (Date("%s")) -> Yes { v = 1 }
                """.formatted(guard, day), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** It fails on 31 December 2026 alone: the year is 2026 before the move and 2027 after it. */
    @Test
    void aGuardThatFailsWhereTheMoveCrossesALineKeepsItsArm() {
        assertTrue(report("Date.year(d) >= 2027 || Date.year(Date.addDays(1, d)) < 2027")
                .contains(OWED));
    }

    /**
     * Whatever way two comparisons of a part of the date and of the date moved by a day are put
     * together, a guard that some date fails keeps its arm.
     *
     * <p>Asked of the dates themselves: the window holds the turn of a year, of every month and
     * of a month's last day, so a guard the calendar fails on is found failing here, and the report
     * is held to owing the arm for it. The converse is not asked, since a guard no date in the
     * window fails may still fail outside it.
     */
    @Test
    void aGuardSomeDateFailsKeepsItsArmWhicheverWayTheMovedPartIsPutBesideTheOwn() {
        String[] parts = {"year", "month", "day"};
        int[] lines = {2027, 2, 28};
        String[] relations = {"<", ">="};
        int[] moves = {1, -1};
        for (int part = 0; part < parts.length; part++) {
            for (String own : relations) {
                for (String moved : relations) {
                    for (int move : moves) {
                        String guard = "Date.%s(d) %s %d || Date.%s(Date.addDays(%d, d)) %s %d"
                                .formatted(parts[part], own, lines[part], parts[part], move, moved,
                                        lines[part]);
                        LocalDate fails = dateWhere(false, parts[part], own, moved, move,
                                lines[part]);
                        LocalDate holds = dateWhere(true, parts[part], own, moved, move,
                                lines[part]);
                        // The row is the date the guard holds of, so it does not cover the arm
                        // itself; a guard no date holds of has no such row to write.
                        if (fails != null && holds != null) {
                            assertTrue(report(guard, holds).contains(OWED), guard);
                        }
                    }
                }
            }
        }
    }

    /** The first date from the end of 2025 to the start of 2028 of which the guard, {@code own}
     *  of its part or else {@code moved} of the part of the date moved by {@code move} days, comes
     *  out as {@code outcome}, or null where there is none. */
    private static LocalDate dateWhere(boolean outcome, String part, String own, String moved,
                                       int move, int line) {
        for (LocalDate day = LocalDate.of(2025, 12, 20); day.isBefore(LocalDate.of(2028, 1, 10));
                day = day.plusDays(1)) {
            boolean guard = holds(part, own, day, line)
                    || holds(part, moved, day.plusDays(move), line);
            if (guard == outcome) {
                return day;
            }
        }
        return null;
    }

    private static boolean holds(String part, String relation, LocalDate day, int line) {
        int value = switch (part) {
            case "year" -> day.getYear();
            case "month" -> day.getMonthValue();
            default -> day.getDayOfMonth();
        };
        return relation.equals("<") ? value < line : value >= line;
    }

    /** And the same part of the same date, contradicting itself, still drops the arm: the move
     *  is what tells two numbers apart, not a reason to stop reading either. */
    @Test
    void aGuardThatHoldsOfTheSameDateWhateverItIsLeavesNoArm() {
        for (String guard : new String[] {
                "Date.year(d) < 2027 || Date.year(d) >= 2027",
                "Date.month(d) < 7 || Date.month(d) >= 7"}) {
            assertFalse(report(guard).contains(OWED), guard);
        }
    }

    /** A year a moved date has is still a year some date has, but it is named by no atom here, so
     *  nothing is said of it: the arm behind a guard on it stays owed rather than dropped. */
    @Test
    void thePartOfAMovedDateSaysNothingOfItsEnds() {
        assertTrue(report("Date.year(Date.addDays(1, d)) < 2030").contains(OWED));
        assertTrue(report("Date.year(Date.addDays(1, d)) < 1000000000").contains(OWED));
    }

    /** The first year a date is written at, from the other end. */
    @Test
    void theFirstYearADateHasEndsTheYearsFromBelow() {
        assertFalse(report("Date.year(d) > -1000000000").contains(OWED));
        assertTrue(report("Date.year(d) > -999999999").contains(OWED));
    }
}
