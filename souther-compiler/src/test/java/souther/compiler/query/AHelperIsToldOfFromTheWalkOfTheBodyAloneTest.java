package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The helper a function applied outside it calls on each element is known from the walk of the
 * body alone: asking for it asks no line where it decides, reads no line against the rows and
 * searches for no row, which is where what a measurement costs is spent.
 */
class AHelperIsToldOfFromTheWalkOfTheBodyAloneTest {

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

    /** That nothing asked where a line decides, read the lines against the rows, or searched. */
    private static void measuredNothing(Compilation compilation) {
        compilation.db().everyAnswer().keySet().forEach(key -> assertFalse(
                key instanceof Adequacy.Dividing || key instanceof Adequacy.Divided
                        || key instanceof Adequacy.Readings
                        || key instanceof Adequacy.BoundarySearch,
                "nothing past the walk of the body was asked: " + key));
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
        assertTrue(one.readings() > 1, one::toString);
        measuredNothing(compilation);
    }

    @Test
    void aFunctionAppliedInsideTheHelperNamesNothing() {
        Compilation compilation = ACompiledModel.measured(SEARCHED_INSIDE_THE_HELPER,
                Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        assertEquals(List.of(), told(compilation));
        assertEquals(List.of(), HelpersReadOnApplicationsAroundThem.toldOf(compilation, null,
                null));
        measuredNothing(compilation);
    }

    /** What an author is told before the measurement: the helper once, with each behavior that
     *  reads it and how often, however few times that is. */
    @Test
    void theHelperIsToldOfOnceWithEveryBehaviorReadingIt() {
        Compilation compilation = ACompiledModel.measured(TWO_BEHAVIORS,
                Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        List<HelpersReadOnApplicationsAroundThem.Said> said =
                HelpersReadOnApplicationsAroundThem.toldOf(compilation, null, null);
        assertEquals(1, said.size(), said::toString);
        assertEquals(new ValueName.Helper(MODULE, "isBusinessDay"), said.getFirst().helper());
        assertEquals(List.of("g", "h"), List.copyOf(said.getFirst().readings().keySet()));
        measuredNothing(compilation);
    }

    /** A behavior the author did not select is asked nothing, where its comparisons stand
     *  included. */
    @Test
    void aBehaviorNotSelectedIsAskedNothing() {
        Compilation compilation = ACompiledModel.measured(TWO_BEHAVIORS,
                Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        List<HelpersReadOnApplicationsAroundThem.Said> said =
                HelpersReadOnApplicationsAroundThem.toldOf(compilation, MODULE, "h");
        assertEquals(1, said.size(), said::toString);
        assertEquals(List.of("h"), List.copyOf(said.getFirst().readings().keySet()));
        compilation.db().everyAnswer().keySet().forEach(key -> assertFalse(
                (key instanceof Adequacy.ComparisonsRead read && !read.behavior().equals("h"))
                        || (key instanceof HelpersReadOnApplicationsAroundThem told
                        && !told.behavior().equals("h")),
                "asked of a behavior not selected: " + key));
    }

    /** Billing's due dates, read by two behaviors. */
    private static final String TWO_BEHAVIORS = SHAPED_AS_BILLING.replace("exposing (g,",
            "exposing (g, h,") + """

            behavior h : (c: Calendar, nominal: Date) -> Date
            let h (c, nominal) = onABusinessDay(c, nominal)
            """;
}
