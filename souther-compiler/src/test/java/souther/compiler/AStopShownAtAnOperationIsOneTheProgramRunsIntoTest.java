package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.diag.SourcePos;
import souther.compiler.execute.RunStop;
import souther.compiler.execute.StepsGotPast;
import souther.compiler.inputs.ABoundThatKeepsEveryRunGoing;
import souther.compiler.inputs.AConstructionStopShown;
import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.EveryRunStops;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.StepWhereARunMayStop;
import souther.compiler.inputs.StepWhereAStopIsNotShown;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatIsShownOfAStop;
import souther.compiler.inputs.WhatKeepsEveryRunGoing;
import souther.compiler.numeric.ExactRatio;
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
import java.util.function.Function;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the report says of the steps a run may stop at is what the program does at those steps.
 *
 * <p>The truth is the program run, through classes generated to say where each step that may end a
 * run is written: a run that stops says the step it stopped at, which steps it got past, and which
 * calls it was inside. A step is where it is written, as the report names a step
 * ({@link StepWhereARunMayStop#at}), so two steps of one operation and one reason are two steps
 * however alike the numbers they stop at, and nothing is read off what a run said it stopped for.
 *
 * <p>Each claim is held to what it says ({@link Oracle}): a stop shown, to the first stop of each
 * run of its witness being at its step; a step said nowhere, to no run of the grid stopping there,
 * a step said not resolved excusing only itself; the rows every run getting to a step stops at, to
 * every run of the grid inside them that gets to the step stopping there; and what keeps every run
 * going, to no run of the grid meeting its bounds stopping at the step past where a number stops.
 * A claim of every run that no run of the grid is about is one nothing here holds, and is said so.
 * The oracle is held to refusing claims moved off their step ({@code aClaimMovedOffItsStep...}).
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
 * decide the forms, and each end a claim of every run names with the number either side of it, so
 * a case costs what running the grid of one behavior does, the forms being behaviors of one module
 * compiled once.
 */
class AStopShownAtAnOperationIsOneTheProgramRunsIntoTest {

    private static final String GREATEST = "9223372036854775807";

    /** The fewest numbers that decide every form below: nought, which a divisor is held at, one,
     *  which a branch is taken at, and the end of an {@code Int}, which a sum passes. */
    private static final List<Long> WHOLE = List.of(0L, 1L, Long.MAX_VALUE);

    /** The places of the input, as the model declares them. */
    private static final List<String> PLACES = List.of("e", "p", "q");

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
        return Module.COMPILED.db().ask(new Adequacy.Divided("demo", behaviorOf(form))).value()
                .stopsShown();
    }

    /** The runs of each form's behavior, made once for every test that holds a claim to them. */
    private static final Map<String, Runs> RUNS = new ConcurrentHashMap<>();

    /** The runs of {@code form}'s behavior over the grid of what is said of it. */
    private static Runs runsOf(String form) {
        return RUNS.computeIfAbsent(form, name -> {
            try {
                return Runs.of(name, saidOf(name));
            } catch (Exception e) {
                throw new AssertionError("the behavior of " + name + " runs", e);
            }
        });
    }

    /** One form is one behavior of the one module, which is as much as the claim about it asks. */
    @ParameterizedTest
    @MethodSource("forms")
    void whatIsSaidOfAStepIsWhatTheProgramDoesThere(String name) throws Exception {
        Form form = FORMS.get(name);
        List<WhatIsShownOfAStop> said = saidOf(name);
        Runs runs = runsOf(name);
        boolean shown = said.stream().anyMatch(StepWhereARunMayStop.class::isInstance);
        boolean everyRunOfTheWayStops = form.required() && everyRunOfTheWayStops(runs);
        assertAll(
                () -> assertEquals(List.of(), Oracle.unheld(said, runs),
                        "what is said of a step is what the runs of the grid do there"),
                () -> assertTrue(!form.required() || everyRunOfTheWayStops,
                        "a form said to stop every run of its way, and a run of the grid on the"
                                + " way gets past what it works out"),
                () -> assertTrue(!everyRunOfTheWayStops || shown,
                        "every run of the way stops, nothing it works out first is one this"
                                + " compiler cannot say it gets past, and no stop is shown"));
    }

    /**
     * Each kind of claim of every run is held to some run of the forms: a claim no run of the grid
     * is about holds of every run there is, and where every claim of a kind were one, the forms
     * would hold that kind to nothing. A step no input gets to is one such, and some forms say
     * them; those are not refused, and are not what holds the kind either.
     */
    @Test
    void eachKindOfClaimOfEveryRunIsHeldToSomeRun() throws Exception {
        int rows = 0;
        int keeping = 0;
        for (String name : FORMS.keySet()) {
            List<WhatIsShownOfAStop> said = saidOf(name);
            Oracle.Held held = Oracle.heldTo(said, runsOf(name));
            rows += held.rowsHeldTo();
            keeping += held.keepingHeldTo();
        }
        assertTrue(rows > 0, "no run of the grid is in the rows every run stops at");
        assertTrue(keeping > 0, "no run of the grid is within what keeps every run going");
    }

    /**
     * A stop shown at one step and moved to another is refused, though the run of its witness
     * stops for the same reason at the same numbers: the run stops at the step it is written at.
     */
    @Test
    void aClaimMovedOffItsStepIsRefusedThoughItsRunStopsForTheSameReason() throws Exception {
        String name = "oneOperationWrittenAtTwoPlaces";
        List<WhatIsShownOfAStop> said = saidOf(name);
        Runs runs = runsOf(name);
        StepWhereARunMayStop stop = said.stream().filter(StepWhereARunMayStop.class::isInstance)
                .map(StepWhereARunMayStop.class::cast).findFirst()
                .orElseThrow(() -> new AssertionError("a stop is shown of " + said));
        SourcePos elsewhere = said.stream().map(WhatIsShownOfAStop::at)
                .filter(at -> !at.equals(stop.at())).findFirst()
                .orElseThrow(() -> new AssertionError("something is said of another step: "
                        + said));
        List<WhatIsShownOfAStop> moved = new ArrayList<>(said);
        moved.set(said.indexOf(stop), new StepWhereARunMayStop(elsewhere, stop.shown(),
                stop.constructions(), stop.everyRunStops(), stop.keeping()));

        assertEquals(List.of(), Oracle.unheld(said, runs));
        assertNotEquals(List.of(), Oracle.unheld(moved, runs));
    }

    /**
     * A step said not resolved excuses itself and no other: with the stop shown at one step taken
     * out, the runs that stop there are said nowhere, whatever else is left not resolved.
     */
    @Test
    void aStepLeftNotResolvedExcusesNoOtherStep() throws Exception {
        for (String name : FORMS.keySet()) {
            List<WhatIsShownOfAStop> said = saidOf(name);
            if (said.stream().noneMatch(StepWhereAStopIsNotShown.class::isInstance)
                    || said.stream().noneMatch(StepWhereARunMayStop.class::isInstance)) {
                continue;
            }
            Runs runs = runsOf(name);
            List<WhatIsShownOfAStop> without = said.stream()
                    .filter(each -> !(each instanceof StepWhereARunMayStop)).toList();
            assertEquals(List.of(), Oracle.unheld(said, runs), name);
            assertNotEquals(List.of(), Oracle.unheld(without, runs), name);
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
    void theRowsEveryRunStopsAtWidenedToEveryRowAreRefused() throws Exception {
        String name = "oneOperationWrittenAtTwoPlaces";
        List<WhatIsShownOfAStop> said = saidOf(name);
        StepWhereARunMayStop stop = said.stream().filter(StepWhereARunMayStop.class::isInstance)
                .map(StepWhereARunMayStop.class::cast)
                .filter(each -> !each.everyRunStops().isEmpty()).findFirst()
                .orElseThrow(() -> new AssertionError("the rows every run stops at are said of "
                        + said));
        Runs runs = runsOf(name);
        EveryRunStops first = stop.everyRunStops().getFirst();
        EveryRunStops everywhere = new EveryRunStops(first.operation(), first.where().stream()
                .map(within -> new EveryRunStops.Within(within.form(),
                        BigInteger.valueOf(Long.MIN_VALUE), null))
                .toList());
        List<WhatIsShownOfAStop> widened = new ArrayList<>(said);
        widened.set(said.indexOf(stop), new StepWhereARunMayStop(stop.at(), stop.shown(),
                stop.constructions(), List.of(everywhere), stop.keeping()));

        assertEquals(List.of(), Oracle.unheld(said, runs));
        assertNotEquals(List.of(), Oracle.unheld(widened, runs));
    }

    /**
     * What keeps every run going, its bounds let out to every value, is refused: on a way every
     * run takes, a run at the greatest value gets to the step and stops there.
     */
    @Test
    void whatKeepsEveryRunGoingLetOutToEveryValueIsRefused() throws Exception {
        String name = "oneOperationWrittenAtTwoPlaces";
        List<WhatIsShownOfAStop> said = saidOf(name);
        StepWhereARunMayStop stop = said.stream().filter(StepWhereARunMayStop.class::isInstance)
                .map(StepWhereARunMayStop.class::cast)
                .filter(each -> each.keeping().isPresent()).findFirst()
                .orElseThrow(() -> new AssertionError("what keeps every run going is said of "
                        + said));
        Runs runs = runsOf(name);
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

        assertEquals(List.of(), Oracle.unheld(said, runs));
        assertNotEquals(List.of(), Oracle.unheld(loosened, runs));
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
    private static boolean everyRunOfTheWayStops(Runs runs) {
        boolean someStops = false;
        for (Run run : runs.grid()) {
            if (run.stopped().isPresent()) {
                someStops = true;
            } else if (!run.answered().equals(Optional.of("3"))) {
                return false;
            }
        }
        return someStops;
    }

    /**
     * One run of the behavior: the input, what it got past and the calls it ended inside, and
     * where it stopped, or what it answered where it did not.
     */
    record Run(Map<String, Long> in, StepsGotPast.Account account, Optional<RunStop> stopped,
               Optional<String> answered) {

        /**
         * The step of the behavior the run stopped at, as a finding of the behavior names a step:
         * the call it ended inside, where it ended inside one, which is the step of this body a
         * stop in another declaration's is at, and where it stopped otherwise. None where it did
         * not stop, or stopped where the code said no place.
         */
        Optional<RunStop.Site> stoppedAt() {
            if (stopped.isEmpty()) {
                return Optional.empty();
            }
            if (!account.inside().isEmpty()) {
                return Optional.of(account.inside().getFirst());
            }
            return switch (stopped.get()) {
                case RunStop.AtAnEnd it -> it.site();
                case RunStop.AtAConstruction it -> it.site();
                case RunStop.AtAnUnreachable it -> it.site();
                case RunStop.AtAnEnsures _ -> Optional.empty();
            };
        }

        /** Whether the run stopped at {@code step} for an operation the language refuses to
         *  finish. */
        boolean endedAt(RunStop.Site step) {
            return stopped.orElse(null) instanceof RunStop.AtAnEnd
                    && stoppedAt().equals(Optional.of(step));
        }

        /** Whether the run got to {@code step}: got past it, or stopped there. */
        boolean gotTo(RunStop.Site step) {
            return account.gotPast().contains(step) || stoppedAt().equals(Optional.of(step));
        }
    }

    /**
     * The runs of one behavior: every run of the grid, and a run of any input asked for, with
     * where each step the report names is written.
     */
    record Runs(Object behavior, Map<Map<String, Long>, Run> held, List<Run> grid,
                Function<SourcePos, Optional<RunStop.Site>> placed) {

        /**
         * The runs of {@code form}'s behavior over the grid of {@code said}: at each place,
         * {@link #WHOLE} and each end a claim of every run names of that place, with the number
         * either side of it. An end is where a claim of every run turns, and a grid without it
         * holds no run the claim is about where every run it holds stops before the step; a place
         * the claim does not weigh is not where it turns.
         */
        static Runs of(String form, List<WhatIsShownOfAStop> said) throws Exception {
            Object behavior = Emitted.behavior(Module.LOADER, "demo", behaviorOf(form))
                    .getConstructor().newInstance();
            Map<String, Set<Long>> values = new LinkedHashMap<>();
            PLACES.forEach(place -> values.put(place, new LinkedHashSet<>(WHOLE)));
            endsNamedBy(said).forEach((place, ends) -> {
                for (BigInteger end : ends) {
                    for (BigInteger near : List.of(end.subtract(BigInteger.ONE), end,
                            end.add(BigInteger.ONE))) {
                        if (near.bitLength() < Long.SIZE) {
                            values.get(place).add(near.longValueExact());
                        }
                    }
                }
            });
            Map<Map<String, Long>, Run> held = new LinkedHashMap<>();
            for (long e : values.get("e")) {
                for (long p : values.get("p")) {
                    for (long q : values.get("q")) {
                        Map<String, Long> in = Map.of("e", e, "p", p, "q", q);
                        held.put(in, run(behavior, in));
                    }
                }
            }
            return new Runs(behavior, new ConcurrentHashMap<>(held), List.copyOf(held.values()),
                    Module.COMPILED::writtenAt);
        }

        /**
         * Every end a claim of every run in {@code said} names, by the place of the input it is an
         * end of: each place a form of the rows weighs, and the place a bound is declared on. A
         * place none of this input's is no place of the grid, and the oracle says it cannot weigh
         * it.
         */
        private static Map<String, List<BigInteger>> endsNamedBy(List<WhatIsShownOfAStop> said) {
            Map<String, List<BigInteger>> out = new LinkedHashMap<>();
            for (WhatIsShownOfAStop each : said) {
                List<EveryRunStops> stops = switch (each) {
                    case StepWhereARunMayStop it -> it.everyRunStops();
                    case StepWhereAStopIsNotShown it -> it.everyRunStops();
                };
                Optional<WhatKeepsEveryRunGoing> kept = switch (each) {
                    case StepWhereARunMayStop it -> it.keeping();
                    case StepWhereAStopIsNotShown it -> it.keeping();
                };
                for (EveryRunStops stop : stops) {
                    for (EveryRunStops.Within within : stop.where()) {
                        for (NumericTerm term : within.form().coefs().keySet()) {
                            if (term instanceof NumericTerm.ValueOf(TermPath place)
                                    && PLACES.contains(Oracle.fieldOf(place))) {
                                Stream.of(within.least(), within.greatest())
                                        .filter(end -> end != null)
                                        .forEach(out.computeIfAbsent(Oracle.fieldOf(place),
                                                _ -> new ArrayList<>())::add);
                            }
                        }
                    }
                }
                kept.ifPresent(region -> region.bounds().forEach(bound -> {
                    if (bound.holder().named().steps().size() == 1
                            && PLACES.contains(bound.holder().named().steps().getFirst())) {
                        out.computeIfAbsent(bound.holder().named().steps().getFirst(),
                                _ -> new ArrayList<>()).add(bound.at());
                    }
                }));
            }
            return out;
        }

        /** The run of {@code in}: the grid's, where the grid holds it. */
        Run of(Map<String, Long> in) {
            return held.computeIfAbsent(in, asked -> {
                try {
                    return run(behavior, asked);
                } catch (Exception e) {
                    throw new AssertionError("the input " + asked + " is one the behavior takes",
                            e);
                }
            });
        }

        private static Run run(Object behavior, Map<String, Long> in) throws Exception {
            Object decoded = Codecs.decoded(Module.LOADER, "demo.In", new LinkedHashMap<>(in));
            StepsGotPast.begin();
            Object answered;
            try {
                answered = Codecs.apply(behavior, decoded);
            } catch (RuntimeException stopped) {
                StepsGotPast.Account account = StepsGotPast.end();
                Optional<RunStop> end = RunStop.ofTheEndOf(stopped);
                if (end.isEmpty()) {
                    throw stopped;
                }
                return new Run(in, account, end, Optional.empty());
            }
            return new Run(in, StepsGotPast.end(), Optional.empty(), Optional.of(String.valueOf(
                    Codecs.encode(Module.LOADER, "demo.Out", answered))));
        }
    }

    /**
     * What a report says of the steps a run may stop at, held to the runs of a grid: each claim
     * the runs do not hold, said. A pure reading of what it is handed, so that it is held as well to
     * refusing claims it is handed wrong.
     */
    static final class Oracle {

        /**
         * What {@link #heldTo} found: each claim the runs do not hold, and how many claims of
         * every run of each kind some run was about. A claim of every run no run is about holds of
         * every run there is, and is no claim the runs held it to; a step no input gets to is one.
         */
        record Held(List<String> unheld, int rowsHeldTo, int keepingHeldTo) {}

        static List<String> unheld(List<WhatIsShownOfAStop> said, Runs runs) {
            return heldTo(said, runs).unheld();
        }

        static Held heldTo(List<WhatIsShownOfAStop> said, Runs runs) {
            List<String> out = new ArrayList<>();
            int[] heldTo = new int[2];
            Set<RunStop.Site> named = new LinkedHashSet<>();
            for (WhatIsShownOfAStop each : said) {
                Optional<RunStop.Site> step = runs.placed().apply(each.at());
                if (step.isEmpty()) {
                    out.add("said of a step written nowhere this compilation lays out: " + each);
                    continue;
                }
                named.add(step.get());
                switch (each) {
                    case StepWhereARunMayStop stops -> {
                        shown(stops, step.get(), runs, out);
                        heldTo[0] += everyRunStops(stops.everyRunStops(), step.get(), runs, out);
                        heldTo[1] += keeping(stops.keeping(), step.get(), runs, out);
                    }
                    case StepWhereAStopIsNotShown open -> {
                        heldTo[0] += everyRunStops(open.everyRunStops(), step.get(), runs, out);
                        heldTo[1] += keeping(open.keeping(), step.get(), runs, out);
                    }
                }
            }
            for (Run run : runs.grid()) {
                if (run.stopped().isEmpty()) {
                    continue;
                }
                Optional<RunStop.Site> at = run.stoppedAt();
                if (at.isEmpty()) {
                    out.add(run.in() + " stops where the code says no place: " + run.stopped());
                } else if (!named.contains(at.get())) {
                    out.add(run.in() + " stops at " + at.get() + ", a step nothing is said of: "
                            + run.stopped());
                }
            }
            return new Held(out, heldTo[0], heldTo[1]);
        }

        /** Each run of a witness of a stop shown at {@code step} stops there first. */
        private static void shown(StepWhereARunMayStop stops, RunStop.Site step, Runs runs,
                                  List<String> out) {
            for (AStopShown shown : stops.shown()) {
                if (!shown.structure().isEmpty()) {
                    out.add("a witness asks of a list, which this input has none of: " + shown);
                    continue;
                }
                for (Map<String, Long> in : completions(shown.at())) {
                    Run run = runs.of(in);
                    if (!run.endedAt(step)) {
                        out.add(shown.operation() + " shown at " + step + ", and the run of " + in
                                + " stops at " + run.stoppedAt() + ": " + run.stopped());
                    }
                }
            }
            for (AConstructionStopShown shown : stops.constructions()) {
                for (Map<String, Long> in : completions(shown.at())) {
                    Run run = runs.of(in);
                    if (!(run.stopped().orElse(null) instanceof RunStop.AtAConstruction)
                            || !run.stoppedAt().equals(Optional.of(step))) {
                        out.add("a construction shown at " + step + ", and the run of " + in
                                + " stops at " + run.stoppedAt() + ": " + run.stopped());
                    }
                }
            }
        }

        /** Every run of the grid inside the rows, getting to {@code step}, stops there. Answers
         *  how many of {@code stops} some run of the grid is about. */
        private static int everyRunStops(List<EveryRunStops> stops, RunStop.Site step, Runs runs,
                                         List<String> out) {
            int heldTo = 0;
            for (EveryRunStops each : stops) {
                boolean about = false;
                for (Run run : runs.grid()) {
                    Optional<Boolean> inside = inside(each.where(), run.in());
                    if (inside.isEmpty()) {
                        out.add("the rows every run stops at weigh what this does not: " + each);
                        return heldTo;
                    }
                    if (!inside.get() || !run.gotTo(step)) {
                        continue;
                    }
                    about = true;
                    if (!run.endedAt(step)) {
                        out.add("every run getting to " + step + " in " + each + " stops there, and"
                                + " the run of " + run.in() + " stops at " + run.stoppedAt()
                                + ": " + run.stopped());
                    }
                }
                heldTo += about ? 1 : 0;
            }
            return heldTo;
        }

        /** No run of the grid meeting the bounds stops at {@code step} past where a number
         *  stops. Answers one where some run of the grid is about what is kept, and none where
         *  none is or nothing is kept. */
        private static int keeping(Optional<WhatKeepsEveryRunGoing> kept, RunStop.Site step,
                                   Runs runs, List<String> out) {
            if (kept.isEmpty()) {
                return 0;
            }
            boolean about = false;
            for (Run run : runs.grid()) {
                Optional<Boolean> meets = meets(kept.get().bounds(), run.in());
                if (meets.isEmpty()) {
                    out.add("what keeps every run going is declared on what this does not weigh: "
                            + kept.get().bounds());
                    return 0;
                }
                if (!meets.get() || !run.gotTo(step)) {
                    continue;
                }
                about = true;
                if (run.endedAt(step)) {
                    out.add("no run within " + kept.get().bounds() + " stops at " + step
                            + ", and the run of " + run.in() + " does: " + run.stopped());
                }
            }
            return about ? 1 : 0;
        }

        /**
         * Every input that holds {@code at} at the places it names, the places it does not name at
         * every value of the grid.
         */
        private static List<Map<String, Long>> completions(List<AStopShown.NumberAt> at) {
            Map<String, Long> named = new LinkedHashMap<>();
            for (AStopShown.NumberAt number : at) {
                named.put(fieldOf(number.place()), number.number().longValueExact());
            }
            List<Map<String, Long>> out = new ArrayList<>();
            for (long e : named.containsKey("e") ? List.of(named.get("e")) : WHOLE) {
                for (long p : named.containsKey("p") ? List.of(named.get("p")) : WHOLE) {
                    for (long q : named.containsKey("q") ? List.of(named.get("q")) : WHOLE) {
                        out.add(Map.of("e", e, "p", p, "q", q));
                    }
                }
            }
            return out;
        }

        /** Whether {@code in} is within every one of {@code where}; none where one weighs a number
         *  that is not the value at a place of the input, or weighs one by other than a whole
         *  number. */
        private static Optional<Boolean> inside(List<EveryRunStops.Within> where,
                                                Map<String, Long> in) {
            boolean inside = true;
            for (EveryRunStops.Within within : where) {
                BigInteger sum = BigInteger.ZERO;
                for (Map.Entry<NumericTerm, ExactRatio> term : within.form().coefs().entrySet()) {
                    BigInteger weight = term.getValue().wholeOrNull();
                    if (weight == null
                            || !(term.getKey() instanceof NumericTerm.ValueOf(TermPath place))
                            || !in.containsKey(fieldOf(place))) {
                        return Optional.empty();
                    }
                    sum = sum.add(weight.multiply(BigInteger.valueOf(in.get(fieldOf(place)))));
                }
                inside &= (within.least() == null || sum.compareTo(within.least()) >= 0)
                        && (within.greatest() == null || sum.compareTo(within.greatest()) <= 0);
            }
            return Optional.of(inside);
        }

        /** Whether {@code in} meets every one of {@code bounds}; none where one is declared on
         *  something other than a field of the input. */
        private static Optional<Boolean> meets(Set<ABoundThatKeepsEveryRunGoing> bounds,
                                               Map<String, Long> in) {
            boolean meets = true;
            for (ABoundThatKeepsEveryRunGoing bound : bounds) {
                if (!(bound.holder() instanceof ABoundThatKeepsEveryRunGoing.Holder.AData data)
                        || !data.data().module().equals("demo")
                        || !data.data().name().equals("In")
                        || data.named().steps().size() != 1
                        || !PLACES.contains(data.named().steps().getFirst())) {
                    return Optional.empty();
                }
                BigInteger value = BigInteger.valueOf(in.get(data.named().steps().getFirst()));
                meets &= bound.atMost() ? value.compareTo(bound.at()) <= 0
                        : value.compareTo(bound.at()) >= 0;
            }
            return Optional.of(meets);
        }

        /** The field of the input {@code place} is. */
        private static String fieldOf(TermPath place) {
            return ((TermPath.Step.Field) place.steps().getLast()).name();
        }

        private Oracle() {}
    }
}
