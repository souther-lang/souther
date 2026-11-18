package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

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

    /** Due dates moved to the first business day of three by the rule each is due under, and,
     *  of them, those that are no business day: by {@code %3$s} over each rule's dates. */
    private static final String MODEL = """
            module demo

            data DueDateRule = SameDay | FollowingBusinessDay
            data Calendar = { holidays: Set<Date>, aSunday: Date, rule: DueDateRule }

            let isBusinessDay (calendar: Calendar, d: Date): Bool =
                Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7) >= 1
                    && Bool.not(Set.contains(d, calendar.holidays))

            let onABusinessDay (calendar: Calendar, nominal: Date): Date =
                match calendar.rule with
                    | SameDay -> nominal
                    | FollowingBusinessDay -> List.rangeInclusive(0, 2)
                        |> List.map(k -> Date.addDays(k, nominal))
                        |> List.find(d -> isBusinessDay(calendar, d))
                        |> Option.withDefault(nominal)

            behavior f : (calendar: Calendar, from: Date, days: Int, rules: List<DueDateRule>)
                -> List<%1$s>
                constructs Calendar

            let f (calendar, from, days, rules) =
                %2$s(rule -> {
                    let ruled = Calendar { ...calendar, rule = rule }
                    List.rangeInclusive(0, days)
                        |> List.map(n -> onABusinessDay(ruled, Date.addDays(n, from)))
                        |> %3$s(d -> Bool.not(isBusinessDay(ruled, d)))
                }, rules)
            """;

    @Test
    void readOnTheElementsTheListStartsWithWhereEveryElementIsAsked() {
        assertEquals(List.of(), aboutARemainderNoPositionHolds(
                MODEL.formatted("Date", "List.flatMap", "List.filter")));
    }

    @Test
    void notReadSoWhereTheRunStopsAtTheFirstElementThatAnswers() {
        assertTrue(aboutARemainderNoPositionHolds(MODEL.formatted("Bool", "List.map", "List.any"))
                .stream().anyMatch(line -> line.contains("isBusinessDay@")));
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
