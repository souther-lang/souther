package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.Located;
import souther.compiler.diag.SourceRendering;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.reach.Reachability;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A closure an operation applies over a container of the input runs only where the container holds
 * something, so where what holds on the way to it leaves the container empty, nothing in it is
 * reached.
 *
 * <p>The arms here are the ones {@code List.filter} branches on with what the closure answers, so
 * none of them is a condition the author wrote: no condition on the way to them is refused, and a
 * reading that asked only the conditions owed each of them a row nobody can write. What shuts them
 * is the closure never being applied, which is the same fact the reading of the comparisons puts on
 * each application ({@link souther.compiler.partition.WhereAClosureIsApplied}).
 */
class AClosureOverAContainerHoldingNoneReachesNothingInsideItTest {

    private static final String HELD = """
            module held
            data Meeting = { owner: Int, n: Int }
            data Ms = List<Meeting> invariant List.length(value) <= %s
            behavior many : (ms: Ms) -> List<Meeting>
            let many (ms) = List.filter(m -> m.n > 5, ms.value)

            example many
                | "none" : (Ms([])) -> []
            """;

    private static final String GUARDED = """
            module guarded
            data Meeting = { owner: Int, n: Int }
            data Ms = { ms: List<Meeting>, k: Int }
            behavior many : (ms: Ms) -> List<Meeting>
            let many (ms) = {
                guard List.length(ms.ms) == 0 else []
                List.filter(m -> m.n > 5, ms.ms)
            }

            example many
                | "some" : (Ms { ms = [Meeting { owner = 1, n = 1 }], k = 0 }) -> []
                | "none" : (Ms { ms = [], k = 0 }) -> []
            """;

    private static final String TWICE = """
            module twice
            data Meeting = { owner: Int, n: Int }
            data Nobody = List<Meeting> invariant List.length(value) <= 0
            data Ms = { a: Nobody, b: List<Meeting> }
            behavior many : (ms: Ms) -> Int
            let pick (xs: List<Meeting>): List<Meeting> = List.filter(m -> m.n > 5, xs)
            let many (ms) = List.length(pick(ms.a.value)) + List.length(pick(ms.b))

            example many
                | "none" : (Ms { a = Nobody([]), b = [] }) -> 0
            """;

    @Test
    void theArmsOfAClosureOverAListHeldToNoneAreReachedByNothing() {
        List<Reachability> inTheClosure = arms(HELD.formatted("0"), "held", true);

        assertEquals(2, inTheClosure.size(), "`List.filter` keeps an element or drops it");
        for (Reachability arm : inTheClosure) {
            Reachability.Unreachable proven = (Reachability.Unreachable) arm;
            assertEquals(List.of("ms"), WhatAnAnswerSays.containersAppliedToNothingIn(
                    proven.proof()), "it is the list the closure is applied over that is empty");
            assertEquals(List.of(), WhatAnAnswerSays.conditionsIn(proven.proof()),
                    "and the rules alone leave it so");
        }
        String report = report(HELD.formatted("0"));
        assertFalse(report.contains("no row goes through"),
                () -> "no row is asked for through an arm nothing reaches:\n" + report);
    }

    @Test
    void aListThatMayHoldOneLeavesThemOpen() {
        List<Reachability> inTheClosure = arms(HELD.formatted("3"), "held", true);

        assertEquals(2, inTheClosure.size());
        assertTrue(inTheClosure.stream().noneMatch(Reachability.Unreachable.class::isInstance),
                () -> "a list that may hold an element is one the closure may be applied to: "
                        + inTheClosure);
    }

    @Test
    void aGuardThatEmptiesTheListShutsThemOnlyUnderIt() {
        List<Reachability> inTheClosure = arms(GUARDED, "guarded", true);
        List<Reachability> written = arms(GUARDED, "guarded", false);

        assertEquals(2, inTheClosure.size());
        for (Reachability arm : inTheClosure) {
            Reachability.Unreachable proven = (Reachability.Unreachable) arm;
            assertEquals(List.of("ms.ms"), WhatAnAnswerSays.containersAppliedToNothingIn(
                    proven.proof()));
            assertEquals(1, WhatAnAnswerSays.conditionsIn(proven.proof()).size(),
                    "what empties the list is the guard on the way to the closure");
        }
        assertTrue(written.stream().noneMatch(Reachability.Unreachable.class::isInstance),
                () -> "the guard itself goes either way: " + written);
    }

    @Test
    void aClosureAlsoAppliedOverAListThatMayHoldOneStaysOwed() {
        String report = report(TWICE);

        assertTrue(report.contains("no row goes through `then`")
                        && report.contains("no row goes through `else`"),
                () -> "the arms are reached through the list that may hold an element:\n"
                        + report);
    }

    /**
     * What arrives at each arm {@code behavior many} is owed, of those written in the library's
     * closure where {@code inTheLibrary}, and of the model's own otherwise.
     */
    private static List<Reachability> arms(String model, String module, boolean inTheLibrary) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code()).toList(),
                "the model under test compiles");
        CoverageSites.Plan plan =
                compilation.db().ask(new Bodies.Observable(module)).value().plan();
        PathReachability.Answers answers =
                compilation.db().ask(new Adequacy.PathReached(module)).value().get("many");
        return plan.arms("many").stream()
                .filter(site -> site.obligation().origin().owner().module()
                        .equals(module) != inTheLibrary)
                .map(site -> answers.at(site.place()))
                .toList();
    }

    private static String report(String model) {
        List<Located> warnings = new ArrayList<>();
        Compilation compilation = Compiler.analyzedModules(List.of(model), ModulePath.EMPTY,
                warnings, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
