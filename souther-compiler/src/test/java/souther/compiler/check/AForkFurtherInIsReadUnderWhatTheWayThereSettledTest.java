package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.reach.PathDecision;
import souther.compiler.reach.Reachability;

import java.util.Comparator;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a fork on the way to a place settled is what a fork there is read under, whichever of the
 * two the first one settled: that one of several things holds, or which case a value is.
 *
 * <p>A path keeps facts that all hold. One of several holding is no such fact, but a part the rest
 * of the way rules out is no way in, so where every part is ruled out nothing arrives, and where one
 * is left it is that one that holds. Which case a value is, is what an arm on the way settled, and a
 * second fork on the same value further in — another {@code match}, or an operation applying a
 * closure to what an optional holds — is read under it.
 */
class AForkFurtherInIsReadUnderWhatTheWayThereSettledTest {

    private static final String ONE_OF = """
            module oneof
            data Meeting = { owner: Int, n: Int }
            data Nobody = List<Meeting> invariant List.length(value) <= 0
            data Ms = { a: Nobody, b: Nobody, n: Int }

            behavior both : (ms: Ms) -> Int
            let both (ms) =
                if List.length(ms.a.value) > 0 || List.length(ms.b.value) > 0 then 1 else 0

            behavior notBoth : (ms: Ms) -> Int
            let notBoth (ms) =
                if List.length(ms.a.value) <= 0 && List.length(ms.b.value) <= 0 then 1 else 0

            behavior oneLeft : (ms: Ms) -> Int
            let oneLeft (ms) =
                if List.length(ms.a.value) > 0 || ms.n > 5 then (if ms.n > 3 then 1 else 2) else 0

            behavior twoLeft : (ms: Ms) -> Int
            let twoLeft (ms) = if ms.n < 0 || ms.n > 5 then (if ms.n > 3 then 1 else 2) else 0

            behavior someMeeting : (ms: Ms) -> Int
            let someMeeting (ms) = if List.any(m -> m.n > 5, ms.a.value) then 1 else 0
            """;

    private static final String CASES = """
            module cases
            data Meeting = { owner: Int, n: Int }
            data North
            data South
            data Region = North | South
            data O = { o: Meeting?, r: Region }
            data Out = { n: Int? }

            behavior applied : (o: O) -> Out
                constructs Out
            let applied (o) = match o.o with
                | Some m -> Out { n = None }
                | None -> Out { n = Option.map(x -> if x.n > 5 then 1 else 0, o.o) }

            behavior again : (o: O) -> Int
            let again (o) = match o.o with
                | Some m -> 0
                | None -> (match o.o with
                    | Some y -> 1
                    | None -> 2)

            behavior where : (o: O) -> Int
            let where (o) = match o.r with
                | North -> (match o.r with
                    | South -> 1
                    | North -> 2)
                | South -> 3
            """;

    private static final String SHORT_CIRCUITS = """
            module circuits

            behavior andAtTheGreatest : (a: Int, b: Int) -> Int
            let andAtTheGreatest (a, b) = {
                guard a == 9223372036854775807 else 0
                if b > 0 && a + 1 > 0 then 1 else 0
            }

            behavior orAtTheGreatest : (a: Int, b: Int) -> Int
            let orAtTheGreatest (a, b) = {
                guard a == 9223372036854775807 else 0
                if b <= 0 || a + 1 <= 0 then 1 else 0
            }

            behavior andBelowTheGreatest : (a: Int, b: Int) -> Int
            let andBelowTheGreatest (a, b) = {
                guard a == 9223372036854775806 else 0
                if b > 0 && a + 1 > 0 then 1 else 0
            }
            """;

    private static final Read ONE_OF_READ = Read.of(ONE_OF, "oneof");
    private static final Read CASES_READ = Read.of(CASES, "cases");
    private static final Read SHORT_CIRCUITS_READ = Read.of(SHORT_CIRCUITS, "circuits");

    /**
     * Where a short circuit's right side answers nothing, the arm for the value the right decides is
     * the one no run enters, and the other is entered by the runs the left settled.
     */
    @Test
    void theArmForTheValueTheRightDecidesIsTheOneNoRunEnters() {
        List<Reachability> and = SHORT_CIRCUITS_READ.arms("andAtTheGreatest", "IF", 0);
        assertInstanceOf(Reachability.Unreachable.class, and.get(0), () -> "" + and);
        assertFalse(and.get(1) instanceof Reachability.Unreachable, () -> "" + and);

        List<Reachability> or = SHORT_CIRCUITS_READ.arms("orAtTheGreatest", "IF", 0);
        assertFalse(or.get(0) instanceof Reachability.Unreachable, () -> "" + or);
        assertInstanceOf(Reachability.Unreachable.class, or.get(1), () -> "" + or);

        List<Reachability> answering = SHORT_CIRCUITS_READ.arms("andBelowTheGreatest", "IF", 0);
        assertFalse(answering.stream().anyMatch(Reachability.Unreachable.class::isInstance),
                () -> "the right answers here, so both values come out: " + answering);
    }

    @Test
    void aDisjunctionEveryPartOfWhichIsRuledOutReachesNothing() {
        List<Reachability> arms = ONE_OF_READ.arms("both", "IF", 0);

        Reachability.Unreachable proven = assertInstanceOf(Reachability.Unreachable.class,
                arms.get(0), () -> "neither list holds anything: " + arms);
        assertEquals(List.of(PathDecision.Way.HELD), ways(proven),
                "what rules it out is the condition itself, held");
        assertFalse(arms.get(1) instanceof Reachability.Unreachable, () -> "" + arms);
    }

    @Test
    void theDenialOfAConjunctionIsADisjunctionAsWell() {
        List<Reachability> arms = ONE_OF_READ.arms("notBoth", "IF", 0);

        assertFalse(arms.get(0) instanceof Reachability.Unreachable, () -> "" + arms);
        assertInstanceOf(Reachability.Unreachable.class, arms.get(1),
                () -> "one of two empty lists holding something is no way in: " + arms);
    }

    @Test
    void theOnePartTheWayLeavesIsTheOneThatHolds() {
        List<Reachability> inner = ONE_OF_READ.arms("oneLeft", "IF", 1);

        assertFalse(inner.get(0) instanceof Reachability.Unreachable, () -> "" + inner);
        assertInstanceOf(Reachability.Unreachable.class, inner.get(1),
                () -> "past an empty list, it is `n > 5` that held, so `n <= 3` is none: "
                        + inner);
    }

    @Test
    void twoPartsTheWayLeavesAreNotTakenAsEitherOne() {
        List<Reachability> inner = ONE_OF_READ.arms("twoLeft", "IF", 1);

        assertFalse(inner.stream().anyMatch(Reachability.Unreachable.class::isInstance),
                () -> "`n < 0` reaches the one and `n > 5` the other: " + inner);
    }

    @Test
    void someElementMeetingSomethingIsTheContainerHoldingOne() {
        List<Reachability> arms = ONE_OF_READ.arms("someMeeting", "IF", 0);

        assertInstanceOf(Reachability.Unreachable.class, arms.get(0),
                () -> "an empty list holds no meeting of any kind: " + arms);
    }

    @Test
    void aClosureOverAnOptionAnArmFoundEmptyReachesNothing() {
        List<Reachability> inTheClosure = CASES_READ.arms("applied", "IF", 0);

        assertEquals(2, inTheClosure.size());
        for (Reachability arm : inTheClosure) {
            Reachability.Unreachable proven = assertInstanceOf(Reachability.Unreachable.class,
                    arm, () -> "the closure is applied to what `o.o` holds: " + inTheClosure);
            assertEquals(List.of("o.o"),
                    WhatAnAnswerSays.containersAppliedToNothingIn(proven.proof()));
            assertEquals(List.of(PathDecision.Way.TAKEN), ways(proven),
                    "and what empties it is the arm on the way, taken");
        }
    }

    @Test
    void aSecondMatchOnAnOptionIsReadUnderTheArmOfTheFirst() {
        List<Reachability> inner = CASES_READ.arms("again", "MATCH", 0);

        Reachability.Unreachable proven = assertInstanceOf(Reachability.Unreachable.class,
                inner.get(0), () -> "under `None`, `o.o` holds nothing: " + inner);
        assertEquals(List.of(PathDecision.Way.TAKEN, PathDecision.Way.TAKEN), ways(proven),
                "the arm outside and this one, each taken");
        assertFalse(inner.get(1) instanceof Reachability.Unreachable, () -> "" + inner);
    }

    @Test
    void aSecondMatchOnASumIsReadUnderTheArmOfTheFirst() {
        List<Reachability> inner = CASES_READ.arms("where", "MATCH", 0);

        assertInstanceOf(Reachability.Unreachable.class, inner.get(0),
                () -> "under `North`, `o.r` is no `South`: " + inner);
        assertFalse(inner.get(1) instanceof Reachability.Unreachable, () -> "" + inner);
    }

    private static List<PathDecision.Way> ways(Reachability.Unreachable proven) {
        return WhatAnAnswerSays.conditionsIn(proven.proof()).stream()
                .map(PathDecision::way).toList();
    }

    /** One model's plan and what arrives at each of its arms, read once. */
    private record Read(String module, CoverageSites.Plan plan,
                        Map<String, PathReachability.Answers> answers) {

        static Read of(String model, String module) {
            Compilation compilation = Compilation.ofSource(model, "Main");
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors().stream()
                            .map(each -> each.diagnostic().code()).toList(),
                    "the model under test compiles");
            return new Read(module,
                    compilation.db().ask(new Bodies.Observable(module)).value().plan(),
                    compilation.db().ask(new Adequacy.PathReached(module)).value());
        }

        /**
         * What arrives at each arm of the fork of {@code kind} the model wrote in
         * {@code behavior}, the {@code rank}th of them in the order the model numbers its forks —
         * an {@code if} before the forks in its arms, a {@code match} after them — in the order its
         * arms are written.
         */
        List<Reachability> arms(String behavior, String kind, int rank) {
            List<ControlPlace.Arm> written = plan.arms(behavior).stream()
                    .map(CoverageSites.ArmSite::place)
                    .filter(place -> place.arm().origin().owner().module().equals(module)
                            && place.arm().origin().kind().name().equals(kind))
                    .toList();
            List<Integer> forks = written.stream()
                    .map(place -> place.arm().origin().ordinal()).distinct().sorted().toList();
            int fork = forks.get(rank);
            return written.stream()
                    .filter(place -> place.arm().origin().ordinal() == fork)
                    .sorted(Comparator.comparingInt(place -> place.arm().part()))
                    .map(place -> answers.get(behavior).at(place))
                    .toList();
        }
    }
}
