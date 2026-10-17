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
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row held past an earlier guard along one of its ways is held past a later one along the same
 * way ({@link HeldOutcome#along}).
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

    /**
     * The earlier guard leaves the value two cases, and a row is held to one of them: two ways
     * that ask the same of every container and tell apart only in which case the value is.
     */
    private static final String CASED = """
            module example.settle

            data No
            data Plain
            data Express
            data Other
            data Kind = Plain | Express | Other

            behavior settle : (kind: Kind, n: Int) -> Bool | No

            let settle (kind, n) = {
                guard Bool.not(kind == Other) else No
                guard n > 0 else No
                true
            }
            """;

    @Test
    void theCaseAnEarlierGuardWasHeldToIsTheCaseOnTheWayToTheLater() {
        Read read = read(CASED);
        HeldOutcome.Bringing.Found earlier =
                assertInstanceOf(HeldOutcome.Bringing.Found.class, read.holding(0));
        HeldOutcome.Bringing.Found later =
                assertInstanceOf(HeldOutcome.Bringing.Found.class, read.holding(1));
        HeldOutcome whole = later.ways().getFirst();
        List<HeldOutcome> eachCase = earlier.ways().stream()
                .filter(one -> !one.chosen().isEmpty()).toList();
        assertEquals(2, eachCase.size(), () -> "the earlier guard is held to either case: "
                + earlier.ways());
        assertNotEquals(eachCase.get(0).reaching().requirements(),
                eachCase.get(1).reaching().requirements(),
                "the two ways ask for two cases");
        for (HeldOutcome each : eachCase) {
            Reachability.Reaching taken = assertInstanceOf(Reachability.Reaching.class,
                    HeldOutcome.along(List.of(each, whole), read.declarations()));
            assertEquals(each.reaching().requirements(), taken.requirements(),
                    () -> "the way to the later guard asks for the case the earlier was held to");
        }
    }

    /**
     * A way the way to the later guard splits into takes the earlier guard along one of its
     * alternatives, which asks of a list the way whole asks nothing of: what holding a row to it
     * asks is that as much as the later guard's own condition, so that a reader asking what
     * holding it writes is told of the list.
     */
    @Test
    void whatHoldingARowAlongASplitWayAsksIncludesTheAlternativeItTakes() {
        Read read = read(MODEL);
        List<HeldOutcome> later = assertInstanceOf(HeldOutcome.Bringing.Found.class,
                read.holding(1)).ways();
        HeldOutcome whole = later.stream().filter(one -> !one.reaching().along().isEmpty())
                .findFirst().orElseThrow();
        List<HeldOutcome> split = later.stream()
                .filter(one -> one.chosen().size() > whole.chosen().size()).toList();
        assertEquals(2, split.size(), () -> "the later way splits at either list: " + later);
        for (HeldOutcome each : split) {
            List<OnTheWay.TakenIn> taken = each.reaching().boundedOnTheWay().stream()
                    .filter(one -> !whole.reaching().boundedOnTheWay().contains(one)).toList();
            assertTrue(!taken.isEmpty() && each.asks().containsAll(taken),
                    () -> "what the split way asks beside the whole is asked: " + taken
                            + " in " + each.asks());
        }
    }

    /** A guard asking one thing of one list, which is no choice of several. */
    private static final String SINGLE = """
            module example.settle

            data No

            behavior settle : (xs: List<Int>, n: Int) -> Bool | No

            let settle (xs, n) = {
                guard List.length(List.filter(x -> x > 0, xs)) >= 1 else No
                guard n > 0 else No
                true
            }
            """;

    /**
     * What an earlier way asked that is no choice — some element of {@code xs} above nought — is
     * asked of the way to a later guard that does not take it in, as much as a choice would be:
     * the row is held to all of it wherever it goes next.
     */
    @Test
    void whatAnEarlierWayAskedThatIsNoChoiceIsAskedOfALaterWayThatLacksIt() {
        Read read = read(SINGLE);
        HeldOutcome earlier = assertInstanceOf(HeldOutcome.Bringing.Found.class,
                read.holding(0)).ways().getFirst();
        assertTrue(earlier.chosen().isEmpty() && !earlier.reaching().boundedOnTheWay().isEmpty(),
                () -> "the earlier way asks of the list and chooses nothing: " + earlier);
        HeldOutcome later = assertInstanceOf(HeldOutcome.Bringing.Found.class,
                read.holding(1)).ways().getFirst();
        HeldOutcome laterAlone = new HeldOutcome(later.demands(), List.of(),
                WayToTheBorder.UNTOUCHED, Map.of(), Reachability.untouched(read.declarations()));
        Reachability.Reaching taken = assertInstanceOf(Reachability.Reaching.class,
                HeldOutcome.along(List.of(earlier, laterAlone), read.declarations()));
        assertTrue(taken.boundedOnTheWay().containsAll(earlier.reaching().boundedOnTheWay()),
                () -> "the way to the later guard asks what the earlier asked: "
                        + taken.boundedOnTheWay());
    }

    /**
     * Two ways of one condition taken together: a row held to some element of {@code xs} above
     * nought and to some element of {@code ys} above nought is held to both, which a row is; a
     * value held to two of its cases is held to what no value is.
     */
    @Test
    void twoWaysOfOneConditionTakenTogetherAreBothOrNone() {
        Read summed = read(MODEL);
        List<HeldOutcome> eachList = assertInstanceOf(HeldOutcome.Bringing.Found.class,
                summed.holding(0)).ways();
        assertEquals(2, eachList.size(), () -> "either list: " + eachList);
        Reachability.Reaching both = assertInstanceOf(Reachability.Reaching.class,
                HeldOutcome.along(eachList, summed.declarations()));
        for (HeldOutcome each : eachList) {
            assertTrue(both.boundedOnTheWay().containsAll(each.reaching().boundedOnTheWay()),
                    () -> "a row along both is held to each: " + both.boundedOnTheWay());
        }
        Read cased = read(CASED);
        List<HeldOutcome> eachCase = assertInstanceOf(HeldOutcome.Bringing.Found.class,
                cased.holding(0)).ways().stream().filter(one -> !one.chosen().isEmpty())
                .toList();
        assertInstanceOf(Reachability.NothingReaches.class,
                HeldOutcome.along(eachCase, cased.declarations()),
                "no value is two of its cases");
    }

    /**
     * A later way that does not take the earlier guard's condition in — a way read through copies,
     * which holds only what every copy's way holds — still asks of the row what the earlier guard
     * was held along: the row has to be that wherever it goes next.
     */
    @Test
    void aChoiceOfAConditionTheLaterWayDoesNotTakeInIsAskedBesideIt() {
        Read read = read(CASED);
        HeldOutcome.Bringing.Found earlier =
                assertInstanceOf(HeldOutcome.Bringing.Found.class, read.holding(0));
        HeldOutcome.Bringing.Found later =
                assertInstanceOf(HeldOutcome.Bringing.Found.class, read.holding(1));
        HeldOutcome laterAlone = new HeldOutcome(later.ways().getFirst().demands(), List.of(),
                WayToTheBorder.UNTOUCHED, Map.of(), Reachability.untouched(read.declarations()));
        for (HeldOutcome each : earlier.ways().stream()
                .filter(one -> !one.chosen().isEmpty()).toList()) {
            Reachability.Reaching taken = assertInstanceOf(Reachability.Reaching.class,
                    HeldOutcome.along(List.of(each, laterAlone), read.declarations()));
            assertEquals(each.reaching().requirements(), taken.requirements(),
                    () -> "the case the earlier guard was held to is asked beside the later way");
        }
    }

    @Test
    void theWayToTheLaterGuardIsTheOneAlongTheWayTheEarlierWasHeldAlong() {
        Read read = read(MODEL);
        HeldOutcome.Bringing.Found earlier =
                assertInstanceOf(HeldOutcome.Bringing.Found.class, read.holding(0));
        HeldOutcome.Bringing.Found later =
                assertInstanceOf(HeldOutcome.Bringing.Found.class, read.holding(1));
        // The later guard's way whole, which splits at the earlier guard.
        HeldOutcome whole = later.ways().stream()
                .filter(one -> !one.reaching().along().isEmpty())
                .findFirst().orElse(null);
        assertNotNull(whole, () -> "the way to the later guard splits at the earlier one: "
                + later.ways());
        // Each of the earlier guard's ways that asks something of one list alone.
        List<HeldOutcome> alongOne = earlier.ways().stream()
                .filter(one -> !whole.reaching().boundedOnTheWay()
                        .containsAll(one.reaching().boundedOnTheWay()))
                .toList();
        assertEquals(2, alongOne.size(), () -> "the earlier guard is held along either list: "
                + earlier.ways());
        for (HeldOutcome each : alongOne) {
            Reachability.Reaching taken = assertInstanceOf(Reachability.Reaching.class,
                    HeldOutcome.along(List.of(each, whole), read.declarations()));
            assertTrue(taken.boundedOnTheWay().containsAll(each.reaching().boundedOnTheWay()),
                    () -> "the way to the later guard asks what the earlier was held to: "
                            + each.reaching().boundedOnTheWay() + " along " + taken);
        }
    }

    /** What each guard of the body, in the order it is written, coming out true asks of a row. */
    private record Read(List<Core.If> guards, ReachingCuts cuts, SearchRegion declarations) {

        HeldOutcome.Bringing holding(int guard) {
            ModelOccurrence at = ModelOccurrence.statedAt(
                    switch (Core.withoutStanding(guards.get(guard).cond())) {
                        case Core.Binary comparison -> comparison.occurrence();
                        case Core.PreservedCall applied -> applied.occurrence();
                        case Core other -> throw new IllegalArgumentException(
                                "a guard on a comparison or an application: " + other);
                    }).orElseThrow();
            return cuts.heldAt(at, true, declarations);
        }
    }

    private static Read read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(),
                () -> "the model under test compiles: " + compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                        .toList());
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
