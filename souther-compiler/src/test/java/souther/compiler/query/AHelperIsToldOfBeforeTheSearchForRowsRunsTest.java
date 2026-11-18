package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The helper a function applied outside it calls on each element is known from the lines as read,
 * before any row is searched for at their points: asking for it asks nothing the search makes.
 */
class AHelperIsToldOfBeforeTheSearchForRowsRunsTest {

    private static final String MODULE = "demo";

    /** Billing's due dates, with one row. */
    private static final String SHAPED_AS_BILLING = """
            module demo exposing (g, Calendar, Rule)
            import List ( map, find, rangeInclusive )
            data Rule = Preceding | Following
            data Calendar = { holidays: Set<Date>, aSunday: Date, rule: Rule }
            let weekday (c: Calendar, d: Date): Int =
                Int.floorMod(Date.daysBetween(c.aSunday, d), 7)
            let isBusinessDay (c: Calendar, d: Date): Bool =
                weekday(c, d) >= 1 && weekday(c, d) <= 5 && Bool.not(Set.contains(d, c.holidays))
            let firstBusinessDay (c: Calendar, from: Date, step: Int): Date =
                rangeInclusive(0, 10)
                    |> map(n -> Date.addDays(n * step, from))
                    |> find(d -> isBusinessDay(c, d))
                    |> Option.withDefault(from)
            let onABusinessDay (c: Calendar, nominal: Date): Date =
                match c.rule with
                    | Preceding -> firstBusinessDay(c, nominal, 0 - 1)
                    | Following -> firstBusinessDay(c, nominal, 1)
            let dueDate (c: Calendar, nominal: Date): Date = onABusinessDay(c, nominal)
            behavior g : (c: Calendar, nominal: Date) -> Date
            let g (c, nominal) = dueDate(c, nominal)

            example g
                | "a Saturday moves on to the Monday" :
                    (Calendar { holidays = Set.fromList([ Date("2026-08-11") ]),
                                aSunday = Date("2026-01-04"), rule = Following },
                     Date("2026-08-08")) -> Date("2026-08-10")
            """;

    /** The search and its comparison in one helper called once: its own applications. */
    private static final String SEARCHED_INSIDE_THE_HELPER = """
            module demo exposing (g)
            import List ( find, rangeInclusive )
            let first (x: Int): Int =
                rangeInclusive(0, 10) |> find(t -> t * 3 > x) |> Option.withDefault(0)
            behavior g : (x: Int) -> Bool
            let g (x) = first(x) > 3

            example g
                | "one row" : (5) -> false
            """;

    private static List<HelpersReadOnApplicationsAroundThem.Told> told(Compilation compilation) {
        List<HelpersReadOnApplicationsAroundThem.Told> told = compilation.db()
                .ask(new HelpersReadOnApplicationsAroundThem(MODULE, "g")).value();
        assertTrue(told != null, "the lines of g were read");
        return told;
    }

    private static void searchedNothing(Compilation compilation) {
        compilation.db().everyAnswer().keySet().forEach(key -> assertFalse(
                key instanceof Adequacy.BoundarySearch,
                "nothing searched for rows: " + key));
    }

    @Test
    void theHelperIsNamedWithEveryHelperCallingItAndNothingIsSearched() {
        Compilation compilation = ACompiledModel.measured(SHAPED_AS_BILLING,
                Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        List<HelpersReadOnApplicationsAroundThem.Told> told = told(compilation);
        assertEquals(1, told.size(), told::toString);
        HelpersReadOnApplicationsAroundThem.Told one = told.getFirst();
        assertEquals(new ValueName.Helper(MODULE, "isBusinessDay"), one.named().helper());
        assertEquals(List.of(new ValueName.Helper(MODULE, "firstBusinessDay"),
                new ValueName.Helper(MODULE, "onABusinessDay"),
                new ValueName.Helper(MODULE, "dueDate")), one.calledInside());
        assertTrue(one.readings() > 0 && one.points() > 0, one::toString);
        searchedNothing(compilation);
    }

    @Test
    void aFunctionAppliedInsideTheHelperNamesNothing() {
        Compilation compilation = ACompiledModel.measured(SEARCHED_INSIDE_THE_HELPER,
                Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        assertEquals(List.of(), told(compilation));
        searchedNothing(compilation);
    }
}
