package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row held past an earlier guard along one of its ways is held past a later one along the same
 * way ({@link Generator#wayToTheLast}).
 *
 * <p>The earlier guard holds where some element of {@code xs} or some element of {@code ys} is
 * above nought, and a row is held to one of the two. The way to the later guard takes the earlier
 * one in whole and splits there; composed along it whole, a row is held to neither list, and the
 * way the earlier guard was held along is lost. Asked of the ways as they are handed to a composer,
 * rather than of the row a search comes to, which a walk over the classes can come to by another
 * road.
 */
class AWayPastALaterGuardIsTakenAlongTheWayAnEarlierOneWasHeldAlongTest {

    private static final String MODEL = """
            module example.settle

            data No

            behavior settle : (xs: List<Int>, ys: List<Int>, n: Int) -> Bool | No

            let settle (xs, ys, n) = {
                guard List.length(List.filter(x -> x > 0, xs))
                        + List.length(List.filter(y -> y > 0, ys)) >= 1 else No
                guard n > 0 else No
                true
            }
            """;

    @Test
    void theWayToTheLaterGuardIsTheOneAlongTheWayTheEarlierWasHeldAlong() {
        Read read = read();
        HeldOutcome.Bringing.Found earlier =
                assertInstanceOf(HeldOutcome.Bringing.Found.class, read.holding(0));
        HeldOutcome.Bringing.Found later =
                assertInstanceOf(HeldOutcome.Bringing.Found.class, read.holding(1));
        // The later guard's way whole, which splits at the earlier guard.
        HeldOutcome whole = later.ways().getLast();
        assertFalse(whole.reaching().along().isEmpty(),
                "the way to the later guard splits at the earlier one: " + whole);
        // Each of the earlier guard's ways that asks something of one list alone.
        List<HeldOutcome> alongOne = earlier.ways().stream()
                .filter(one -> !whole.reaching().boundedOnTheWay()
                        .containsAll(one.reaching().boundedOnTheWay()))
                .toList();
        assertEquals(2, alongOne.size(), () -> "the earlier guard is held along either list: "
                + earlier.ways());
        for (HeldOutcome each : alongOne) {
            Reachability.Reaching taken = Generator.wayToTheLast(List.of(each, whole));
            assertTrue(taken.boundedOnTheWay().containsAll(each.reaching().boundedOnTheWay()),
                    () -> "the way to the later guard asks what the earlier was held to: "
                            + each.reaching().boundedOnTheWay() + " along " + taken);
        }
    }

    /** What each guard of the body, in the order it is written, coming out true asks of a row. */
    private record Read(List<Core.If> guards, ReachingCuts cuts, SearchRegion declarations) {

        HeldOutcome.Bringing holding(int guard) {
            Core condition = Core.withoutStanding(guards.get(guard).cond());
            ModelOccurrence at = ModelOccurrence.statedAt(
                    ((Core.Binary) condition).occurrence()).orElseThrow();
            return cuts.heldAt(at, true, declarations);
        }
    }

    private static Read read() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Map<String, InputDomain> inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value();
        AnalysisBody analysis = checked.analysisBodies().get("settle");
        GuardThresholds.Guards guards = ThresholdFixtures.guardsOf("settle", analysis,
                checked.behaviorBodies().get("settle"), checked.plan(), inputs.get("settle"),
                rules);
        List<Core.If> forks = new ArrayList<>();
        collect(analysis.core(), forks);
        return new Read(forks, guards.reaching(),
                inputs.get("settle").reading(rules).quantities().region());
    }

    /** Every fork of {@code e}, outermost first. */
    private static void collect(Core e, List<Core.If> into) {
        if (e instanceof Core.If fork) {
            into.add(fork);
        }
        Core.forEachChild(e, child -> collect(child, into));
    }
}
