package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.ABoundThatKeepsEveryRunGoing;
import souther.compiler.inputs.EveryRunStops;
import souther.compiler.inputs.StepWhereARunMayStop;
import souther.compiler.inputs.StepWhereAStopIsNotShown;
import souther.compiler.inputs.WhatIsShownOfAStop;
import souther.compiler.inputs.WhatKeepsEveryRunGoing;
import souther.compiler.inputs.WhyAConstructionStopIsNotShown;
import souther.compiler.inputs.WhyAStopIsNotShown;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the report says of the steps a run may stop at is what the program does at those steps, as
 * {@link StopsHeldToTheRuns} holds it, over forms of whole numbers; and the oracle refuses each kind
 * of claim handed it wrong by the check of that kind and by no other.
 *
 * <p>Each step of these forms stops a run for one reason, so a step is held to where a run stops
 * and not to why: two reasons at one step would be told apart by nothing here.
 *
 * <p>And a stop is shown of a form that says it is {@code required}: every run of its way stops,
 * which the program says and this does not take on trust. How the report words a finding is held
 * elsewhere.
 *
 * <p>Each form is a case of its own, one model of one behavior, and a form is in the list for the
 * mechanism that turns its case red where it is taken out. The grid is the three numbers that
 * decide the forms, widened by the ends the claims of every run name, so a case costs what running
 * the grid of one behavior does, the forms being behaviors of one module compiled once.
 */
class AStopShownAtAnOperationIsOneTheProgramRunsIntoTest {

    private static final String GREATEST = "9223372036854775807";

    /** The fewest numbers that decide every form below: nought, which a divisor is held at, one,
     *  which a branch is taken at, and the end of an {@code Int}, which a sum passes. */
    private static final List<Object> WHOLE = List.of(0L, 1L, Long.MAX_VALUE);

    /** The input every form takes. */
    private static final StopsHeldToTheRuns.Input INPUT = new StopsHeldToTheRuns.Input("demo", "In",
            Map.of("e", WHOLE, "p", WHOLE, "q", WHOLE));

    /**
     * A comparison, and the way the program takes to it.
     *
     * @param required whether a stop is to be shown of it: every run of the way stops, which the
     *                 program says ({@link #everyRunOfTheWayStops}), and nothing a run works out
     *                 before the stop is a thing this compiler cannot say it gets past
     */
    private record Form(String way, String comparison, boolean required) {

        Form(String way, String comparison) {
            this(way, comparison, false);
        }
    }

    private static final Map<String, Form> FORMS = new LinkedHashMap<>();

    /** The forms a run of the grid stops at a step of that the findings say is not resolved and
     *  show no stop at, each with why the findings say so: a stop the compiler learns to show
     *  moves out of it. */
    private static final Map<String, Set<Enum<?>>> NOT_SHOWN = new LinkedHashMap<>();

    /** The forms a claim of every run of which no run of the grid is about, each with why: a
     *  step no input gets to, which the claim holds of whatever it says. */
    private static final Map<String, String> NOT_ABOUT = new LinkedHashMap<>();

    static {
        // a quotient worked out after the sum is not got to, so is not asked to be away from
        // nought: the way holds the divisor there
        FORMS.put("aQuotientAfterTheSum", new Form("q >= " + GREATEST + " && p == 0",
                "Rational.toInt(DOWN, (q + 1) / p) >= 2", true));
        // a quotient beside the sum and worked out after it is not asked either: the run ends in
        // the sum, not at the divisor it holds at nought
        FORMS.put("aQuotientBesideAndAfterTheSum", new Form("q >= " + GREATEST + " && p == 0",
                "(q + 1) + Rational.toInt(DOWN, e / p) >= 2", true));
        // nor is a branch that stands after it, whose call ends a run for what nothing says
        FORMS.put("aBranchAfterTheSum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, (q + 1) / p) + (if e > 0 then h(e) else 0) >= 2", true));
        // a quotient is stopped at all the same, with what stands after it left untold
        FORMS.put("aCallAfterTheQuotient", new Form("p == 0",
                "Rational.toInt(DOWN, e / p) + h(e) >= 2", true));
        // a quotient worked out before the sum is got past: the stop is where its divisor is not
        // nought, and where its divisor is no form of the input's numbers, it is not shown
        FORMS.put("aQuotientBeforeTheSum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, (e / p) / (q + 1)) >= 2"));
        FORMS.put("aQuotientOfNoFormBeforeTheSum", new Form("q >= " + GREATEST,
                "Rational.toInt(DOWN, (e / (p * p)) / (q + 1)) >= 2"));
        // the body of a let has no place among what a run always works out, and is worked out
        // after the sum all the same: a run that stops at the sum has not got to it
        FORMS.put("aLetBodyAfterTheSum", new Form("q >= " + GREATEST,
                "(q + 1) + { let t = e\n q + 2 } >= 2", true));
        // a call before the sum that stops every run of the way is not got past
        FORMS.put("aCallBeforeTheSumThatStops", new Form("q >= " + GREATEST + " && p == 0",
                "h(p) + (q + 1) >= 2"));
        // a choice read arm by arm stops on one arm and not the other: what is said of the
        // quotient is said of the runs that take its arm, whichever arm a reading was on
        FORMS.put("aStopOnOneArmOfAChoice", new Form("q == 0",
                "(if e > 0 then e else Rational.toInt(DOWN, 4 / p)) >= 2"));
        // the same where the arm's answer settles the comparison whatever it is: no line is drawn
        // on that arm, and a run taking it still works the quotient out
        FORMS.put("aStopOnAnArmThatSettlesTheComparison", new Form("q == 0",
                "(if e > 0 then e else Rational.toInt(DOWN, 1 / p)) >= 2"));
        // the same, the choice given to a name the comparison reads
        FORMS.put("aChoiceGivenToAName", new Form("p == 0",
                "{ let c = if e > 0 then q + 1 else e\n c + 1 } >= 2"));
        // and a helper choosing between arms, called on what the same helper answered
        FORMS.put("aChoiceOnAChoice", new Form("e == e",
                "k(k(e, p), q) >= 2"));
        // a rule that reads a quotient on each sign of its divisor holds its rows away from a
        // divisor of nought, and the run that divides by nought stops all the same, where the
        // quotient is worked out right of an && or in a helper on an arm
        FORMS.put("aQuotientRightOfAnAnd", new Form("q == 0",
                "e > 0 && Rational.toInt(DOWN, 4 / p) >= 2"));
        FORMS.put("aQuotientInAHelperOnAnArm", new Form("q == 0",
                "(if e > 0 then e else m(p)) >= 2"));
        // a rule that reads a rounding on the number before it holds its rows within what an Int
        // holds, and the run whose number rounds past that stops all the same
        FORMS.put("aRoundingPastAnInt", new Form("p == 0",
                "Rational.toInt(DOWN, (q / 1) * (q / 1)) >= 2"));
        // the same on an arm, whose comparison the rule reads as nothing it can draw a line on:
        // what a run taking the arm works out is kept by that reading all the same
        FORMS.put("aRoundingPastAnIntOnAnArm", new Form("p == 0",
                "(if e > 0 then e else Rational.toInt(DOWN, (q / 1) * (q / 1))) >= 2"));
        // what an arm a run does not take works out is nothing a run getting past it met: the
        // sum after the choice stops where q is the greatest Int, whichever arm was taken
        FORMS.put("anArmNotTakenBeforeTheSum", new Form("e == e",
                "{ let r = if p == 0 then q + 2 else 0\n q + 1 } >= 2"));
        // inside a closure the quotient's own dividend is worked out before the division: a run
        // where it passes the ends stops there and not at the divisor
        FORMS.put("aQuotientInAClosureWhoseDividendStopsFirst", new Form("e == e",
                "List.length(List.map(x -> Rational.toInt(DOWN, (q + 1) / p), [1])) >= 2"));
        // a closure applied before the sum is worked out before it: a run whose application
        // divides by nought stops there and does not get to the sum
        FORMS.put("aSumAfterAClosureThatStops", new Form("e == e",
                "{ let xs = List.map(x -> Rational.toInt(DOWN, 4 / p), [1])\n"
                        + " q + 1 + List.length(xs) } >= 2"));
        // a construction a fold makes of what the step before it answered: the second
        // application is handed the first one's answer, and its construction refuses it. It is
        // read in that application's names, and what the application before it works out is
        // not read in its own, so a run is not shown to get past it and the construction is said
        // not resolved: not required to be shown
        FORMS.put("aConstructionOfWhatAFoldCarried", new Form("e == e",
                "List.fold((a, x) -> { let s = Small { value = a + x }\n a + x }, 0, [5, 6])"
                        + " >= 2"));
        NOT_SHOWN.put("aConstructionOfWhatAFoldCarried",
                Set.of(WhyAConstructionStopIsNotShown.REACH_NOT_SHOWN));
        // one closure applied to two elements stops on the second: a run that gets to it on the
        // first gets past it
        FORMS.put("oneSiteOnTwoApplications", new Form("e == e",
                "List.length(List.map(x -> x + 1, [0, q])) >= 2"));
        // one operation written at two places, alike in the numbers they stop at: a run stops at
        // the first and never gets to the second
        FORMS.put("oneOperationWrittenAtTwoPlaces", new Form("e == e",
                "(p + 1) + (p + 1) > q"));
        // two quotients of one dividend, whose runs stop for one reason with one dividend
        FORMS.put("twoQuotientsOfOneDividend", new Form("e == e",
                "Rational.toInt(DOWN, e / p) + Rational.toInt(DOWN, e / q) >= 2"));
        // a sum of two places, whose rows every run stops at are a form of both: its end is at
        // no value of either alone
        FORMS.put("aSumOfTwoPlaces", new Form("e == e", "p + q > e"));
        // two steps kept going by one region, each bound of which is said at one of them
        FORMS.put("twoStepsKeptByOneRegion", new Form("e == e", "p + 1 > e && q + 1 > e"));
        // a helper inlined here and in a behavior called here: a run stopping in the behavior
        // stops at the helper's step written where the one here is, and is said by the call
        FORMS.put("aHelperInlinedHereAndInABehaviorCalledHere", new Form("e == e",
                "g(q) + hg(p) > e"));

        // A run of the grid stops at a step these say is not resolved, for why they say it. A
        // quotient whose divisor is no form of the input's numbers, a rounding and a call tell no
        // operation the run stops in; what is worked out after a step that may stop, the second
        // of two quotients among them, is not shown to be got to.
        NOT_SHOWN.put("aQuotientOfNoFormBeforeTheSum", Set.of(WhyAStopIsNotShown.NO_OPERATION_TOLD,
                WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP));
        NOT_SHOWN.put("aCallBeforeTheSumThatStops", Set.of(WhyAStopIsNotShown.NO_OPERATION_TOLD));
        NOT_SHOWN.put("aRoundingPastAnInt", Set.of(WhyAStopIsNotShown.NO_OPERATION_TOLD));
        NOT_SHOWN.put("aRoundingPastAnIntOnAnArm", Set.of(WhyAStopIsNotShown.NO_OPERATION_TOLD));
        NOT_SHOWN.put("anArmNotTakenBeforeTheSum", Set.of(WhyAStopIsNotShown.NO_VALUE_FOUND));
        NOT_SHOWN.put("aSumAfterAClosureThatStops",
                Set.of(WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP));
        NOT_SHOWN.put("twoQuotientsOfOneDividend",
                Set.of(WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP));
        NOT_SHOWN.put("aHelperInlinedHereAndInABehaviorCalledHere", Set.of(
                WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP,
                WhyAStopIsNotShown.NO_OPERATION_TOLD));

        // A claim of every run about a step no input of the way gets to: every run that would
        // be within it stops at a step before.
        NOT_ABOUT.put("aLetBodyAfterTheSum", "the sum before the let's body stops every run of"
                + " the way, which holds q at the greatest Int");
        NOT_ABOUT.put("aCallBeforeTheSumThatStops", "the call before the sum stops every run of"
                + " the way, which holds p at nought");
        NOT_ABOUT.put("aHelperInlinedHereAndInABehaviorCalledHere", "a run with q at the greatest"
                + " Int stops in the helper before the sum the rows are of");
    }

    static Stream<String> forms() {
        return FORMS.keySet().stream();
    }

    /**
     * The module of every form, one behavior for each, compiled when the first is run, and the
     * loader of its classes generated to say where runs stop.
     */
    private static final class Module {

        static final Compilation COMPILED = compile();
        static final ClassLoader LOADER = COMPILED.loaderSayingWhereRunsStop("demo")
                .orElseThrow(() -> new AssertionError("the module is generated to say where runs"
                        + " stop"));

        private static Compilation compile() {
            StringBuilder model = new StringBuilder("""
                    module demo

                    data In = { e: Int, p: Int, q: Int }
                    data Out = Int

                    data Small = Int
                        invariant value <= 10

                    behavior h : (z: Int) -> Int
                    let h (z) = Rational.toInt(DOWN, 1 / z)

                    let k (a: Int, b: Int): Int =
                        if a > 0 then a else Rational.toInt(DOWN, 1 / b)

                    let m (b: Int): Int = Rational.toInt(DOWN, 4 / b)

                    let g (a: Int): Int = a + 1

                    behavior hg : (z: Int) -> Int
                    let hg (z) = g(z)
                    """);
            for (Map.Entry<String, Form> each : FORMS.entrySet()) {
                String behavior = behaviorOf(each.getKey());
                model.append("""

                        behavior %1$s : (i: In) -> Out constructs %4$s
                        let %1$s (i) = Out { value = if %2$s then (if %3$s then 1 else 2) else 3 }
                        """.formatted(behavior, onTheInput(each.getValue().way()),
                        onTheInput(each.getValue().comparison()),
                        each.getValue().comparison().contains("Small {") ? "Out, Small" : "Out"));
            }
            return ACompiledModel.measured(model.toString(),
                    new Adequacy.Asked(Adequacy.Level.OFF, false));
        }
    }

    private static String behaviorOf(String form) {
        return "b" + new ArrayList<>(FORMS.keySet()).indexOf(form);
    }

    /** What the report says of the stops of {@code form}'s behavior. */
    private static List<WhatIsShownOfAStop> saidOf(String form) {
        return StopsHeldToTheRuns.saidOf(Module.COMPILED, "demo", behaviorOf(form));
    }

    /** The runs of each form's behavior, made once for every test that holds a claim to them. */
    private static final Map<String, StopsHeldToTheRuns.Runs> RUNS = new ConcurrentHashMap<>();

    /** The runs of {@code form}'s behavior over the grid of what is said of it. */
    private static StopsHeldToTheRuns.Runs runsOf(String form) {
        return RUNS.computeIfAbsent(form, name -> new StopsHeldToTheRuns.Runs(Module.COMPILED,
                Module.LOADER, INPUT, behaviorOf(name), saidOf(name)));
    }

    /** One form is one behavior of the one module, which is as much as the claim about it asks. */
    @ParameterizedTest
    @MethodSource("forms")
    void whatIsSaidOfAStepIsWhatTheProgramDoesThere(String name) {
        Form form = FORMS.get(name);
        List<WhatIsShownOfAStop> said = saidOf(name);
        StopsHeldToTheRuns.Runs runs = runsOf(name);
        StopsHeldToTheRuns.Held held = StopsHeldToTheRuns.heldTo(said, runs);
        boolean shown = said.stream().anyMatch(StepWhereARunMayStop.class::isInstance);
        boolean everyRunOfTheWayStops = form.required() && everyRunOfTheWayStops(runs);
        assertAll(
                () -> assertEquals(List.of(), held.unheld(),
                        "what is said of a step is what the runs of the grid do there"),
                () -> assertEquals(List.of(), held.notHeldTo(),
                        "what is said is held to the runs, every claim of it"),
                () -> assertEquals(NOT_SHOWN.getOrDefault(name, Set.of()),
                        held.notShownBecause(), "a run stops at a step said not resolved, for"
                                + " the reasons written down: " + held.notShown()),
                () -> assertEquals(NOT_ABOUT.containsKey(name), !held.notAbout().isEmpty(),
                        "a claim of every run no run of the grid is about, as written down: "
                                + held.notAbout()),
                () -> assertTrue(!form.required() || everyRunOfTheWayStops,
                        "a form said to stop every run of its way, and a run of the grid on the"
                                + " way gets past what it works out"),
                () -> assertTrue(!everyRunOfTheWayStops || shown,
                        "every run of the way stops, nothing it works out first is one this"
                                + " compiler cannot say it gets past, and no stop is shown"));
    }

    /**
     * A stop in a behavior called here, at a step written where one here is by a helper inlined
     * into both, is said by the call and by nothing else: with what is said of the call taken
     * out, the stop is said nowhere, though the step here written at the same place is still
     * said. Only the check that every stop is said has anything to refuse.
     */
    @Test
    void aStopInsideACallIsSaidByTheCallAndNotByAStepWrittenAtTheSamePlace() {
        String name = "aHelperInlinedHereAndInABehaviorCalledHere";
        List<WhatIsShownOfAStop> said = saidOf(name);
        StopsHeldToTheRuns.Runs runs = runsOf(name);
        StopsHeldToTheRuns.Run insideTheCall = runs.grid().stream()
                .filter(run -> run.endedInsideACall().isPresent()).findFirst()
                .orElseThrow(() -> new AssertionError("some run stops inside the call"));
        assertTrue(said.stream().anyMatch(each -> runs.placed(each.at())
                        .equals(insideTheCall.firstStopAt())),
                "the step the run stops at in the behavior is written where one here is: " + said);
        List<WhatIsShownOfAStop> withoutTheCall = said.stream().filter(each ->
                !runs.placed(each.at()).equals(insideTheCall.endedInsideACall().get())).toList();

        assertEquals(Set.of(), StopsHeldToTheRuns.heldTo(said, runs).refused());
        assertEquals(Set.of(StopsHeldToTheRuns.Claim.EVERY_STOP_SAID),
                StopsHeldToTheRuns.heldTo(withoutTheCall, runs).refused());
    }

    /**
     * A stop shown at a step it is not at is refused as a stop shown, though the run of its
     * witness stops for the same reason at the same numbers: the run stops at the step it is
     * written at. Said beside the stop shown where it is, so every stop is still said and only
     * the check of a stop shown has anything to refuse.
     */
    @Test
    void aStopShownAtAnotherStepIsRefusedThoughItsRunStopsForTheSameReason() {
        String name = "oneOperationWrittenAtTwoPlaces";
        List<WhatIsShownOfAStop> said = saidOf(name);
        StopsHeldToTheRuns.Runs runs = runsOf(name);
        StepWhereARunMayStop stop = said.stream().filter(StepWhereARunMayStop.class::isInstance)
                .map(StepWhereARunMayStop.class::cast).findFirst()
                .orElseThrow(() -> new AssertionError("a stop is shown of " + said));
        SourcePos elsewhere = said.stream().map(WhatIsShownOfAStop::at)
                .filter(at -> !at.equals(stop.at())).findFirst()
                .orElseThrow(() -> new AssertionError("something is said of another step: "
                        + said));
        List<WhatIsShownOfAStop> beside = new ArrayList<>(said);
        beside.add(new StepWhereARunMayStop(elsewhere, stop.shown(), stop.constructions(),
                List.of(), Optional.empty()));

        assertEquals(Set.of(), StopsHeldToTheRuns.heldTo(said, runs).refused());
        assertEquals(Set.of(StopsHeldToTheRuns.Claim.A_STOP_SHOWN),
                StopsHeldToTheRuns.heldTo(beside, runs).refused());
    }

    /**
     * A step said not resolved excuses itself and no other: with the stops shown taken out of a
     * form that says other steps not resolved, the runs that stop where they were are said
     * nowhere. Only the check that every stop is said has anything to refuse.
     */
    @Test
    void aStepLeftNotResolvedExcusesNoOtherStep() {
        for (String name : FORMS.keySet()) {
            List<WhatIsShownOfAStop> said = saidOf(name);
            Set<SourcePos> open = new LinkedHashSet<>();
            said.stream().filter(StepWhereAStopIsNotShown.class::isInstance)
                    .forEach(each -> open.add(each.at()));
            if (open.isEmpty() || said.stream().noneMatch(each ->
                    each instanceof StepWhereARunMayStop && !open.contains(each.at()))) {
                continue;
            }
            StopsHeldToTheRuns.Runs runs = runsOf(name);
            List<WhatIsShownOfAStop> without = said.stream()
                    .filter(each -> !(each instanceof StepWhereARunMayStop)).toList();

            assertEquals(Set.of(), StopsHeldToTheRuns.heldTo(said, runs).refused(), name);
            assertEquals(Set.of(StopsHeldToTheRuns.Claim.EVERY_STOP_SAID),
                    StopsHeldToTheRuns.heldTo(without, runs).refused(), name);
            return;
        }
        throw new AssertionError("some form says a stop is shown at one step and not resolved at"
                + " another");
    }

    /**
     * The rows every run getting to a step stops at, widened to every row, are refused: on a way
     * every run takes, a run outside them gets to the step and past it.
     */
    @Test
    void theRowsEveryRunStopsAtWidenedToEveryRowAreRefused() {
        String name = "oneOperationWrittenAtTwoPlaces";
        List<WhatIsShownOfAStop> said = saidOf(name);
        StepWhereARunMayStop stop = said.stream().filter(StepWhereARunMayStop.class::isInstance)
                .map(StepWhereARunMayStop.class::cast)
                .filter(each -> !each.everyRunStops().isEmpty()).findFirst()
                .orElseThrow(() -> new AssertionError("the rows every run stops at are said of "
                        + said));
        StopsHeldToTheRuns.Runs runs = runsOf(name);
        EveryRunStops first = stop.everyRunStops().getFirst();
        EveryRunStops everywhere = new EveryRunStops(first.operation(), first.where().stream()
                .map(within -> new EveryRunStops.Within(within.form(),
                        BigInteger.valueOf(Long.MIN_VALUE), null))
                .toList());
        List<WhatIsShownOfAStop> widened = new ArrayList<>(said);
        widened.set(said.indexOf(stop), new StepWhereARunMayStop(stop.at(), stop.shown(),
                stop.constructions(), List.of(everywhere), stop.keeping()));

        assertEquals(Set.of(), StopsHeldToTheRuns.heldTo(said, runs).refused());
        assertEquals(Set.of(StopsHeldToTheRuns.Claim.EVERY_RUN_STOPS),
                StopsHeldToTheRuns.heldTo(widened, runs).refused());
    }

    /**
     * What keeps every run going, its bounds let out to every value, is refused: on a way every
     * run takes, a run at the greatest value gets to the step and stops there.
     */
    @Test
    void whatKeepsEveryRunGoingLetOutToEveryValueIsRefused() {
        String name = "oneOperationWrittenAtTwoPlaces";
        List<WhatIsShownOfAStop> said = saidOf(name);
        StepWhereARunMayStop stop = said.stream().filter(StepWhereARunMayStop.class::isInstance)
                .map(StepWhereARunMayStop.class::cast)
                .filter(each -> each.keeping().isPresent()).findFirst()
                .orElseThrow(() -> new AssertionError("what keeps every run going is said of "
                        + said));
        StopsHeldToTheRuns.Runs runs = runsOf(name);
        WhatKeepsEveryRunGoing kept = stop.keeping().orElseThrow();
        Set<ABoundThatKeepsEveryRunGoing> letOut = new LinkedHashSet<>();
        for (ABoundThatKeepsEveryRunGoing bound : kept.bounds()) {
            letOut.add(new ABoundThatKeepsEveryRunGoing(bound.holder(), bound.atMost(),
                    BigInteger.valueOf(bound.atMost() ? Long.MAX_VALUE : Long.MIN_VALUE),
                    bound.bound()));
        }
        List<WhatIsShownOfAStop> loosened = new ArrayList<>(said);
        loosened.set(said.indexOf(stop), stop.keptBy(Optional.of(new WhatKeepsEveryRunGoing(
                letOut, kept.held(), Set.of(), kept.shownTogether()))));

        assertEquals(Set.of(), StopsHeldToTheRuns.heldTo(said, runs).refused());
        assertEquals(Set.of(StopsHeldToTheRuns.Claim.KEEPING),
                StopsHeldToTheRuns.heldTo(loosened, runs).refused());
    }

    /**
     * The rows over two places every run stops at, moved one in, are refused: a run whose two
     * numbers come to the greatest {@code Int} together is then within them, and its sum stops
     * nowhere. A form of two places is weighed of both, and the grid holds runs on its end.
     */
    @Test
    void theRowsOverTwoPlacesMovedOneInAreRefused() {
        String name = "aSumOfTwoPlaces";
        List<WhatIsShownOfAStop> said = saidOf(name);
        StepWhereARunMayStop stop = said.stream().filter(StepWhereARunMayStop.class::isInstance)
                .map(StepWhereARunMayStop.class::cast)
                .filter(each -> each.everyRunStops().stream().anyMatch(rows -> rows.where()
                        .stream().anyMatch(within -> within.form().coefs().size() == 2)))
                .findFirst()
                .orElseThrow(() -> new AssertionError("rows over two places are said: " + said));
        EveryRunStops first = stop.everyRunStops().getFirst();
        EveryRunStops movedIn = new EveryRunStops(first.operation(), first.where().stream()
                .map(within -> new EveryRunStops.Within(within.form(),
                        within.least() == null ? null : within.least().subtract(BigInteger.ONE),
                        within.greatest() == null ? null
                                : within.greatest().add(BigInteger.ONE)))
                .toList());
        List<WhatIsShownOfAStop> moved = new ArrayList<>(said);
        moved.set(said.indexOf(stop), new StepWhereARunMayStop(stop.at(), stop.shown(),
                stop.constructions(), List.of(movedIn), stop.keeping()));

        assertEquals(Set.of(), StopsHeldToTheRuns.heldTo(said, runsOf(name)).refused());
        assertEquals(Set.of(StopsHeldToTheRuns.Claim.EVERY_RUN_STOPS),
                StopsHeldToTheRuns.heldTo(moved, runsOf(name)).refused());
    }

    /**
     * One region keeps two steps going, its bounds said one at each: held as the one region it
     * is, with some run within it getting to the steps, and refused where the bound said at one
     * step is let out, though what is said at the other step is unchanged.
     */
    @Test
    void oneRegionSaidAtTwoStepsIsHeldAsOneRegion() {
        String name = "twoStepsKeptByOneRegion";
        List<WhatIsShownOfAStop> said = saidOf(name);
        StopsHeldToTheRuns.Runs runs = runsOf(name);
        List<StepWhereARunMayStop> kept = said.stream()
                .filter(StepWhereARunMayStop.class::isInstance)
                .map(StepWhereARunMayStop.class::cast)
                .filter(each -> each.keeping().isPresent()).toList();
        assertTrue(kept.size() >= 2, "the region's bounds are said at two steps: " + said);
        StopsHeldToTheRuns.Held held = StopsHeldToTheRuns.heldTo(said, runs);
        assertEquals(List.of(), held.unheld());
        assertEquals(List.of(), held.notAbout());
        StepWhereARunMayStop one = kept.getFirst();
        Set<ABoundThatKeepsEveryRunGoing> letOut = new LinkedHashSet<>();
        for (ABoundThatKeepsEveryRunGoing bound : one.keeping().orElseThrow().bounds()) {
            letOut.add(new ABoundThatKeepsEveryRunGoing(bound.holder(), bound.atMost(),
                    BigInteger.valueOf(bound.atMost() ? Long.MAX_VALUE : Long.MIN_VALUE),
                    bound.bound()));
        }
        WhatKeepsEveryRunGoing region = one.keeping().orElseThrow();
        List<WhatIsShownOfAStop> loosened = new ArrayList<>(said);
        loosened.set(said.indexOf(one), one.keptBy(Optional.of(new WhatKeepsEveryRunGoing(
                letOut, region.held(), Set.of(), region.shownTogether()))));

        assertEquals(Set.of(StopsHeldToTheRuns.Claim.KEEPING),
                StopsHeldToTheRuns.heldTo(loosened, runs).refused());
    }

    /** {@code text} over the fields of the input {@code i}. */
    private static String onTheInput(String text) {
        return text.replaceAll("\\be\\b", "i.e").replaceAll("\\bp\\b", "i.p")
                .replaceAll("\\bq\\b", "i.q");
    }

    /**
     * Whether some run of the grid stops and none gets past the way's comparison. A run off the
     * way answers {@code 3} and a run on it that stops answers nothing, so a run that answers one
     * or two is a run on the way that does not stop.
     */
    private static boolean everyRunOfTheWayStops(StopsHeldToTheRuns.Runs runs) {
        boolean someStops = false;
        for (StopsHeldToTheRuns.Run run : runs.grid()) {
            if (run.stopped().isPresent()) {
                someStops = true;
            } else if (!answered(run).equals("3")) {
                return false;
            }
        }
        return someStops;
    }

    /** What {@code run} answered, as the output encodes it. */
    private static String answered(StopsHeldToTheRuns.Run run) {
        try {
            return String.valueOf(Codecs.encode(Module.LOADER, "demo.Out",
                    run.answered().orElseThrow()));
        } catch (Exception e) {
            throw new AssertionError("an answer of Out is encoded", e);
        }
    }
}
