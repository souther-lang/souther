package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A date built for the parts a rule named stands at a value for the parts it did not, and that
 * value rules out no date the calendar has.
 *
 * <p>The parts of a date are not independent the way the parts of a time are: how far the days run
 * depends on the month, and how far February runs depends on the year. So a value chosen for a part
 * nobody asked for is not merely a value that part can take — every one of those builds a date on
 * its own — it has to be the one that leaves every combination still writable.
 *
 * <p>Chosen for each part alone, a month and a day asked for together are offered in whichever year
 * the month-alone case happened to name. The twenty-ninth of February is then a day the calendar
 * has that nothing composes a row for, and the point it was asked at comes back as one nothing
 * could build a representative for — which says the model admits no such date.
 *
 * <p><b>And the dependency is still there.</b> What this holds is that a default rules nothing out,
 * never that a date exists for whatever a rule names. The thirtieth of February and the thirty-first
 * of April are days no date has, and the points asking for them stay empty.
 */
class APartNobodyAskedForRulesOutNoDateTheCalendarHasTest {

    private static String model(String above, String line) {
        return """
                module example.date

                data Yes = { v: Int }
                data No = { why: Int }

                behavior on : (d: Date) -> Yes | No
                    constructs Yes
                    constructs No

                let on (d) = {
                    guard ABOVE else No { why = 0 }
                    guard LINE else No { why = 1 }
                    Yes { v = 1 }
                }
                """.replace("ABOVE", above).replace("LINE", line);
    }

    /**
     * A month and a day, with the year left to whatever this offers: the day exists in some year,
     * so a row is composed for it.
     */
    @Test
    void theTwentyNinthOfFebruaryIsWrittenWhenNoYearWasAskedFor() {
        assertFalse(nothingComposedFor("Date.month(d) == 2", "Date.day(d) < 29", "Date.day(d) = 29"),
                "a leap year has that day, so the point asking for it has a row");
    }

    /** And a day February never has stays empty, whatever year this offers. */
    @Test
    void theThirtiethOfFebruaryIsNotWritten() {
        assertTrue(nothingComposedFor("Date.month(d) == 2", "Date.day(d) < 30", "Date.day(d) = 30"),
                "no year has a thirtieth of February");
    }

    /**
     * And the dependency is the month's and not February's, so a month that is merely short is the
     * same answer.
     */
    @Test
    void theThirtyFirstOfAShortMonthIsNotWritten() {
        assertTrue(nothingComposedFor("Date.month(d) == 4", "Date.day(d) < 31", "Date.day(d) = 31"),
                "April has thirty days");
    }

    /**
     * And where the year was asked for, it is the year the rule named and not the one this offers:
     * a leap year has the day.
     */
    @Test
    void aYearTheRuleNamedIsTheYearTheDayIsAskedOf() {
        assertFalse(nothingComposedFor("Date.year(d) == 2024 && Date.month(d) == 2",
                        "Date.day(d) < 29", "Date.day(d) = 29"),
                "that February has a twenty-ninth");
        assertTrue(nothingComposedFor("Date.year(d) == 2026 && Date.month(d) == 2",
                        "Date.day(d) < 29", "Date.day(d) = 29"),
                "and that one does not, which is the calendar and not this choice");
    }

    /** Whether the point reading {@code subject} is one nothing composed a row for. */
    private static boolean nothingComposedFor(String above, String line, String subject) {
        List<String> empty = new ArrayList<>();
        for (String each : human(model(above, line)).split("\n")) {
            if (each.contains("nothing composed one") && each.contains(subject)) {
                empty.add(each.trim());
            }
        }
        assertTrue(empty.size() <= 1, () -> "one point reads that: " + empty);
        return !empty.isEmpty();
    }

    private static String human(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
