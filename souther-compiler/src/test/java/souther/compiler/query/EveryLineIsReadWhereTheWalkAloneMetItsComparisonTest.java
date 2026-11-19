package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.partition.AComparisonRead;
import souther.compiler.types.AnApplicationOfAClosure;
import souther.compiler.types.ApplicationsReadOn;
import souther.compiler.types.ModelOccurrence;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The walk that says only where each comparison stands ({@link Adequacy.ComparisonsRead}) meets
 * every comparison the walk that draws the lines reads, in the same copy and on every application
 * a line of it was read on.
 *
 * <p>The two are one walk that parts only at what is done at a construct, and this is what keeps
 * them one: a way into a closure, an arm or a helper changed for the one and not the other would
 * leave a line read at a copy, or on an application, the other did not meet, and a helper told of
 * ahead of the measurement would be told of off a body the measurement does not read.
 *
 * <p>Held one way only. The walk that reads nothing also meets a comparison whose statement is
 * carried past it and an application that states nothing of its own, which draw no line.
 */
class EveryLineIsReadWhereTheWalkAloneMetItsComparisonTest {

    private static final String MODULE = "demo";

    /** Billing's due dates: a helper's comparisons inside a find, on each arm of a match. */
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
            behavior g : (c: Calendar, nominal: Date) -> Date
            let g (c, nominal) = onABusinessDay(c, nominal)

            example g
                | "a Saturday moves on to the Monday" :
                    (Calendar { holidays = Set.fromList([ Date("2026-08-11") ]),
                                aSunday = Date("2026-01-04"), rule = Following },
                     Date("2026-08-08")) -> Date("2026-08-10")
            """;

    /** A closure inside a closure, over a list the input holds and one written out. */
    private static final String NESTED = """
            module demo exposing (g)
            import List ( any )
            behavior g : (xs: List<Int>) -> Bool
            let g (xs) = any(x -> any(y -> x + y > 10, xs), [1, 2, 3])

            example g
                | "one row" : ([4, 9]) -> true
            """;

    /** A helper with a search of its own, called on each arm of an if. */
    private static final String SEARCHED_INSIDE_A_HELPER_ON_TWO_ARMS = """
            module demo exposing (g)
            import List ( find, rangeInclusive )
            let first (x: Int, step: Int): Int =
                rangeInclusive(0, 6) |> find(t -> t * step > x) |> Option.withDefault(0)
            behavior g : (x: Int, up: Bool) -> Bool
            let g (x, up) = (if up then first(x, 2) else first(x, 3)) > 3

            example g
                | "one row" : (5, true) -> false
            """;

    @Test
    void billingsDueDates() {
        everyLineIsReadWhereTheWalkAloneMetIt(SHAPED_AS_BILLING);
    }

    @Test
    void aClosureInsideAClosure() {
        everyLineIsReadWhereTheWalkAloneMetIt(NESTED);
    }

    @Test
    void aSearchInsideAHelperOnTwoArms() {
        everyLineIsReadWhereTheWalkAloneMetIt(SEARCHED_INSIDE_A_HELPER_ON_TWO_ARMS);
    }

    private static void everyLineIsReadWhereTheWalkAloneMetIt(String model) {
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        List<AComparisonRead> met = compilation.db()
                .ask(new Adequacy.ComparisonsRead(MODULE, "g")).value();
        LineReadings read = compilation.db().ask(new Adequacy.Readings(MODULE, "g")).value();
        assertNotNull(met, "where g's comparisons stand");
        assertNotNull(read, "g's lines as read");
        Map<ModelOccurrence, Set<AnApplicationOfAClosure>> applied = new HashMap<>();
        for (AComparisonRead each : met) {
            Set<AnApplicationOfAClosure> on =
                    applied.computeIfAbsent(each.copy(), _ -> new HashSet<>());
            for (ApplicationsReadOn one : each.applications()) {
                on.addAll(one.each());
            }
        }
        assertFalse(read.each().isEmpty(), "g reads some line");
        for (BorderAssessment line : read.each()) {
            for (ModelOccurrence copy : line.readAt().inOrder()) {
                Set<AnApplicationOfAClosure> on = applied.get(copy);
                assertNotNull(on, () -> "a line read at a copy the walk alone did not meet: "
                        + copy + " of " + line.border().label());
                assertTrue(on.containsAll(line.readOn().each()), () -> "a line of " + copy
                        + " read on applications the walk alone did not meet it on: "
                        + line.readOn().each() + " beside " + on);
            }
        }
    }
}
