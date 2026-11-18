package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A day a search finds in a list written out, bound before a comparison reads it, is worked out
 * as the list is: a run builds every element before the search looks at any, and what working an
 * element out may stop a run at is told of the comparison. A remainder the search's condition
 * takes by a number written down stops no run ({@link ARemainderByANumberWrittenDownEndsNoRunTest}),
 * so the condition adds nothing to it.
 *
 * <p>Here the day is the nominal day whichever way the search comes out, and whether a set holds
 * it is read over every value: a run gets to the comparison for any day the nominal one is, at
 * the first element of the walk.
 */
class ADaySearchedForInAListWrittenOutIsWorkedOutAsTheListIsTest {

    private static final String MODEL = """
            module demo

            data Calendar = { holidays: Set<Date>, aSunday: Date }

            let isBusinessDay (calendar: Calendar, d: Date): Bool =
                Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7) >= 1
                    && Bool.not(Set.contains(d, calendar.holidays))

            let landed (calendar: Calendar, nominal: Date): Date =
                [nominal]
                    |> List.find(d -> isBusinessDay(calendar, d))
                    |> Option.withDefault(nominal)

            behavior f : (calendar: Calendar, from: Date, days: Int) -> List<Date>

            let f (calendar, from, days) =
                List.rangeInclusive(0, days)
                    |> List.map(n -> landed(calendar, Date.addDays(n, from)))
                    |> List.filter(d -> Bool.not(Set.contains(d, calendar.holidays)))
            """;

    @Test
    void whetherTheSetHoldsTheDayIsReadOverEveryValue() {
        assertEquals(List.of(), unread(MODEL));
    }

    /** The lines of the report saying what was not read. */
    private static List<String> unread(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not read:"))
                .toList();
    }
}
