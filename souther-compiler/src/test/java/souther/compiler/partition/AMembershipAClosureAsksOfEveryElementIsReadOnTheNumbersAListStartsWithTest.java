package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Whether a set holds a day a closure is handed, the day worked out from the element of a list of
 * every whole number between two, is the comparison the law of the membership holds of an
 * element of the set and that day; where the day is chosen by what a remainder of it leaves, that
 * comparison weighs the remainder too. Read inside a closure a run applies to every element it is
 * handed, it is read on the elements the list starts with, as a comparison written there is.
 *
 * <p>Inside one a run applies only until some element answers, the elements a list starts with
 * are not every element a row is asked about, and the remainder is no position's.
 */
class AMembershipAClosureAsksOfEveryElementIsReadOnTheNumbersAListStartsWithTest {

    /** Each day of a list of days moved to the first business day of two, and those of them the
     *  calendar holds: by {@code %2$s} over the days. */
    private static final String MODEL = """
            module demo

            data Calendar = { holidays: Set<Date>, aSunday: Date }

            let isBusinessDay (calendar: Calendar, d: Date): Bool =
                Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7) >= 1
                    && Bool.not(Set.contains(d, calendar.holidays))

            let landed (calendar: Calendar, nominal: Date): Date =
                [nominal, Date.addDays(1, nominal)]
                    |> List.find(d -> isBusinessDay(calendar, d))
                    |> Option.withDefault(nominal)

            behavior f : (calendar: Calendar, from: Date, days: Int) -> %1$s

            let f (calendar, from, days) =
                List.rangeInclusive(0, days)
                    |> List.map(n -> landed(calendar, Date.addDays(n, from)))
                    |> %2$s(d -> Set.contains(d, calendar.holidays))
            """;

    @Test
    void readOnTheElementsTheListStartsWithWhereEveryElementIsAsked() {
        assertEquals(List.of(), aboutARemainderNoPositionHolds(
                MODEL.formatted("List<Date>", "List.filter")));
    }

    @Test
    void notReadSoWhereTheRunStopsAtTheFirstElementThatAnswers() {
        assertFalse(aboutARemainderNoPositionHolds(MODEL.formatted("Bool", "List.any"))
                .isEmpty());
    }

    /** The lines of the report saying a comparison was not read for being about a remainder of
     *  a number no position holds. */
    private static List<String> aboutARemainderNoPositionHolds(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not read:")
                        && line.contains("what a division leaves of a number the body works out"))
                .toList();
    }
}
