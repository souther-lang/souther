package souther.compiler;

import souther.compiler.diag.SourcePos;
import souther.compiler.execute.RunStop;
import souther.compiler.execute.StepsGotPast;
import souther.compiler.inputs.ABoundThatKeepsEveryRunGoing;
import souther.compiler.inputs.AConstructionStopShown;
import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.EveryRunStops;
import souther.compiler.inputs.InputFact;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.StepWhereARunMayStop;
import souther.compiler.inputs.StepWhereAStopIsNotShown;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatIsShownOfAStop;
import souther.compiler.inputs.WhatKeepsEveryRunGoing;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * What the findings of a behavior say of the steps a run may stop at, held to what the program does
 * at them: the one oracle every test of stops against the program run asks.
 *
 * <p>The truth is the program run, through classes generated to say where each step that may end a
 * run is written ({@link Compilation#loaderSayingWhereRunsStop}): a run that stops says the step it
 * stopped at, which steps it got past, and which calls it was inside. A step is where it is
 * written, as a finding names a step ({@link WhatIsShownOfAStop#at}), so two steps of one operation
 * and one reason are two steps, and nothing is read off what a run said it stopped for.
 *
 * <p>Each claim is held to what it says ({@link Claim}): a stop shown, to the first stop of each run
 * of its witness being at its step; a stop of the grid, to a finding naming its step, a step said
 * not resolved excusing only itself; the rows every run getting to a step stops at, to every run of
 * the grid inside them that gets to the step stopping there; and what keeps every run going, to no
 * run of the grid meeting its bounds stopping at the step past where a number stops.
 *
 * <p>What this cannot hold a claim to it says, and does not pass over ({@link Held#notHeldTo}): a
 * region weighing what is no value at a place of the input, a witness too long to build. What is a
 * stop the runs make and the findings leave not resolved, and what is said not resolved where no run
 * of the grid stops, it says as well: a test holds each to what it has written down, so a stop the
 * compiler learns to show, or a step it learns to rule out, moves out of what is written.
 */
final class StopsHeldToTheRuns {

    /** The longest list a witness is built of and run: past it a run is no test of a moment. */
    private static final int MOST_ELEMENTS = 1_000;

    private StopsHeldToTheRuns() {
    }

    /**
     * The input of the behaviors a test runs: the data they take, and the values each of its
     * places takes on the grid — a {@code Long}, a {@code BigDecimal} or a {@code List<Long>} at
     * each, as the data declares the place. The one choice of which values a place takes, for the
     * grid and for the places a witness leaves open alike.
     *
     * @param module the module the data is declared in
     * @param data   the data, which every behavior takes as its one parameter
     * @param values the values each place takes, in the order the data declares its places
     */
    record Input(String module, String data, Map<String, List<Object>> values) {

        Input {
            values = Collections.unmodifiableMap(new LinkedHashMap<>(values));
        }
    }

    /**
     * One run of a behavior: the input, what it got past and the calls it ended inside, and where
     * it stopped, or what it answered where it did not.
     */
    record Run(Map<String, Object> in, StepsGotPast.Account account, Optional<RunStop> stopped,
               Optional<Object> answered) {

        /**
         * The step the run stopped at first, as the code that ended it said, in whichever
         * declaration's body it is written. None where it did not stop, or the code said no place.
         * What the run did, and what every claim of where a run stops is held to.
         */
        Optional<RunStop.Site> firstStopAt() {
            return stopped.flatMap(end -> switch (end) {
                case RunStop.AtAnEnd it -> it.site();
                case RunStop.AtAConstruction it -> it.site();
                case RunStop.AtAnUnreachable it -> it.site();
                case RunStop.AtAnEnsures _ -> Optional.<RunStop.Site>empty();
            });
        }

        /**
         * The call of the behavior's own body the run ended inside, where it stopped inside one:
         * written there, or none where the call is written nowhere the code was told of. None at
         * all where it stopped at a step of the body itself.
         *
         * <p>What a finding of the behavior is about and not where the run stopped. A finding
         * names the steps of its own body, and a stop in another declaration's body is one it
         * names by the call; so this answers only which step a finding has to name for the stop
         * to be said, and nothing a claim of where a run stops is held to.
         */
        Optional<Optional<RunStop.Site>> endedInsideACall() {
            return (stopped.isEmpty() || account.inside().isEmpty()) ? Optional.empty()
                    : Optional.of(account.inside().getFirst());
        }

        /** The step a finding of the behavior has to name for the stop to be said: the call it
         *  ended inside, where it ended inside one, and where it stopped first otherwise. */
        Optional<RunStop.Site> stepToSay() {
            return endedInsideACall().orElse(firstStopAt());
        }

        /** Whether the run stopped first at {@code step}, for an operation the language refuses to
         *  finish. */
        boolean endedAt(RunStop.Site step) {
            return stopped.orElse(null) instanceof RunStop.AtAnEnd
                    && firstStopAt().equals(Optional.of(step));
        }

        /** Whether the run got to {@code step}: got past it, or stopped there first. */
        boolean gotTo(RunStop.Site step) {
            return account.gotPast().contains(step) || firstStopAt().equals(Optional.of(step));
        }
    }

    /**
     * The runs of one behavior: the values each place of the input takes, every run of the grid
     * they make, and a run of any input asked for, with where each step a finding names is written.
     */
    static final class Runs {

        private final Object behavior;
        private final ClassLoader loader;
        private final Input input;
        private final Map<String, Set<Object>> values;
        private final Map<Map<String, Object>, Run> held = new ConcurrentHashMap<>();
        private final List<Run> grid;
        private final Compilation compiled;

        /**
         * The runs of {@code behavior}, of {@code compiled} loaded by {@code loader}, over the
         * grid of {@code input} widened by {@code said}: at each place, the values {@code input}
         * gives it, and each end a claim of every run in {@code said} names of that place with
         * the number either side of it. An end is where a claim of every run turns, and a grid
         * without it holds no run the claim is about where every run it holds stops before the
         * step; a place the claim does not weigh is not where it turns.
         */
        Runs(Compilation compiled, ClassLoader loader, Input input, String behavior,
             List<WhatIsShownOfAStop> said) {
            this.compiled = compiled;
            this.loader = loader;
            this.input = input;
            try {
                this.behavior = Emitted.behavior(loader, input.module(), behavior)
                        .getConstructor().newInstance();
            } catch (ReflectiveOperationException e) {
                throw new AssertionError("the behavior " + behavior + " is generated", e);
            }
            Map<String, Set<Object>> widened = new LinkedHashMap<>();
            input.values().forEach((place, each) -> widened.put(place, new LinkedHashSet<>(each)));
            // An end of a number is put at its place; an end of an element, as the one element of a
            // list at the place of the list.
            endsNamedBy(said).forEach((place, ends) -> {
                Object sample = widened.get(place).iterator().next();
                for (BigInteger end : ends) {
                    for (BigInteger near : List.of(end.subtract(BigInteger.ONE), end,
                            end.add(BigInteger.ONE))) {
                        if (near.bitLength() >= Long.SIZE) {
                            continue;
                        }
                        if (sample instanceof Long) {
                            widened.get(place).add(near.longValueExact());
                        } else if (sample instanceof List<?>) {
                            widened.get(place).add(List.of(near.longValueExact()));
                        }
                    }
                }
            });
            this.values = widened;
            List<Run> out = new ArrayList<>();
            for (Map<String, Object> in : product(new ArrayList<>(widened.keySet()), 0,
                    new LinkedHashMap<>())) {
                out.add(of(in));
            }
            this.grid = List.copyOf(out);
        }

        /** Every run of the grid. */
        List<Run> grid() {
            return grid;
        }

        /** Where {@code at} is written, as a run says a step. */
        Optional<RunStop.Site> placed(SourcePos at) {
            return compiled.writtenAt(at);
        }

        /** The run of {@code in}: the grid's, where the grid holds it. */
        Run of(Map<String, Object> in) {
            return held.computeIfAbsent(Map.copyOf(in), this::run);
        }

        /**
         * Every input that holds {@code at} at the places it names and {@code structure} of the
         * lists it names, the places it names nothing of at every value the grid takes there; none
         * where it names what is no place of the input, or a list longer than a witness is built
         * of.
         */
        Optional<List<Map<String, Object>>> completions(List<AStopShown.NumberAt> at,
                                                        List<InputFact> structure) {
            Map<String, Set<Object>> fixed = new LinkedHashMap<>();
            for (AStopShown.NumberAt number : at) {
                Optional<String> place = placeOf(number.place());
                if (place.isEmpty() || !values.containsKey(place.get())) {
                    return Optional.empty();
                }
                Object sample = values.get(place.get()).iterator().next();
                fixed.put(place.get(), Set.of(sample instanceof BigDecimal
                        ? new BigDecimal(number.number()) : number.number().longValueExact()));
            }
            Map<String, List<Long>> lists = new LinkedHashMap<>();
            for (InputFact fact : structure) {
                if (fact instanceof InputFact.ListLength(TermPath list, int length)) {
                    Optional<String> place = placeOf(list);
                    if (place.isEmpty() || length > MOST_ELEMENTS) {
                        return Optional.empty();
                    }
                    lists.put(place.get(), new ArrayList<>(Collections.nCopies(length, 0L)));
                }
            }
            for (InputFact fact : structure) {
                if (fact instanceof InputFact.ListElement(TermPath list, int index,
                                                          BigInteger number)) {
                    Optional<String> place = placeOf(list);
                    if (place.isEmpty() || !lists.containsKey(place.get())) {
                        return Optional.empty();
                    }
                    lists.get(place.get()).set(index, number.longValueExact());
                }
            }
            lists.forEach((place, list) -> fixed.put(place, Set.of(List.copyOf(list))));
            Map<String, Set<Object>> taken = new LinkedHashMap<>(values);
            taken.putAll(fixed);
            List<Map<String, Object>> out = new ArrayList<>();
            List<String> places = new ArrayList<>(taken.keySet());
            collect(places, 0, new LinkedHashMap<>(), taken, out);
            return Optional.of(out);
        }

        private List<Map<String, Object>> product(List<String> places, int from,
                                                  Map<String, Object> so) {
            List<Map<String, Object>> out = new ArrayList<>();
            collect(places, from, so, values, out);
            return out;
        }

        private static void collect(List<String> places, int from, Map<String, Object> so,
                                    Map<String, Set<Object>> taken,
                                    List<Map<String, Object>> out) {
            if (from == places.size()) {
                out.add(new LinkedHashMap<>(so));
                return;
            }
            for (Object value : taken.get(places.get(from))) {
                so.put(places.get(from), value);
                collect(places, from + 1, so, taken, out);
            }
            so.remove(places.get(from));
        }

        /** Every end a claim of every run in {@code said} names, by the place of the input it is
         *  an end of: each place a form of the rows weighs, and the place a bound is declared on. */
        private Map<String, List<BigInteger>> endsNamedBy(List<WhatIsShownOfAStop> said) {
            Map<String, List<BigInteger>> out = new LinkedHashMap<>();
            for (WhatIsShownOfAStop each : said) {
                for (EveryRunStops stop : everyRunStopsOf(each)) {
                    for (EveryRunStops.Within within : stop.where()) {
                        for (NumericTerm term : within.form().coefs().keySet()) {
                            Optional<String> place = term instanceof NumericTerm.ValueOf(
                                    TermPath path) ? placeOf(path).or(() -> elementOf(path))
                                    : Optional.empty();
                            if (place.isEmpty() || !input.values().containsKey(place.get())) {
                                continue;
                            }
                            for (BigInteger end : new BigInteger[] {within.least(),
                                    within.greatest()}) {
                                if (end != null) {
                                    out.computeIfAbsent(place.get(), _ -> new ArrayList<>())
                                            .add(end);
                                }
                            }
                        }
                    }
                }
                keepingOf(each).ifPresent(kept -> kept.bounds().forEach(bound ->
                        fieldBounded(bound, input).ifPresent(place ->
                                out.computeIfAbsent(place, _ -> new ArrayList<>())
                                        .add(bound.at()))));
            }
            return out;
        }

        private Run run(Map<String, Object> in) {
            try {
                Object decoded = Codecs.decoded(loader, input.module() + "." + input.data(),
                        new LinkedHashMap<>(in));
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
                return new Run(in, StepsGotPast.end(), Optional.empty(), Optional.of(answered));
            } catch (RuntimeException e) {
                throw e;
            } catch (Exception e) {
                throw new AssertionError("the input " + in + " is one the behavior takes", e);
            }
        }
    }

    /**
     * Which claim a run does not hold: each kind is refused by one check and by no other, so a test
     * that hands a claim of one kind wrong is told whether that check refused it.
     */
    enum Claim {
        /** A finding of a step that is written nowhere this compilation lays out. */
        A_STEP_WRITTEN_SOMEWHERE,
        /** A stop shown at a step: each run of its witness stops there first. */
        A_STOP_SHOWN,
        /** Every stop of the grid is at a step some finding names. */
        EVERY_STOP_SAID,
        /** A stop says where it is: the code that ended a run said the step. */
        EVERY_STOP_PLACED,
        /** The rows every run getting to a step stops at. */
        EVERY_RUN_STOPS,
        /** What keeps every run getting to a step going. */
        KEEPING
    }

    /** One claim a run does not hold, and how. */
    record Unheld(Claim claim, String how) {}

    /**
     * What {@link #heldTo} found.
     *
     * @param unheld                    each claim the runs do not hold
     * @param notHeldTo                 each claim nothing here can hold to a run, and why: a region
     *                                  over what is no value at a place, a witness too long to build
     * @param notShown                  each step a run of the grid stops at that no finding shows a
     *                                  stop at, and only one saying it is not resolved names, with
     *                                  why each finding there says so
     * @param notResolvedWhereNoneStops each step said not resolved that no run of the grid stops at
     * @param rowsHeldTo                how many claims of the rows every run stops at some run of
     *                                  the grid is about
     * @param keepingHeldTo             how many claims of what keeps every run going some run of the
     *                                  grid is about
     */
    record Held(List<Unheld> unheld, List<String> notHeldTo,
                Map<RunStop.Site, Set<Enum<?>>> notShown,
                Set<RunStop.Site> notResolvedWhereNoneStops, int rowsHeldTo, int keepingHeldTo) {

        /** The kinds of claim held wrong. */
        Set<Claim> refused() {
            Set<Claim> out = new LinkedHashSet<>();
            unheld.forEach(each -> out.add(each.claim()));
            return out;
        }

        /** Why the steps a run stops at and no stop is shown at are said not resolved, every
         *  reason any of them is said with. */
        Set<Enum<?>> notShownBecause() {
            Set<Enum<?>> out = new LinkedHashSet<>();
            notShown.values().forEach(out::addAll);
            return out;
        }
    }

    /** What {@code said} holds of {@code runs}, and what it does not. */
    static Held heldTo(List<WhatIsShownOfAStop> said, Runs runs) {
        List<Unheld> out = new ArrayList<>();
        List<String> notHeldTo = new ArrayList<>();
        int[] heldTo = new int[2];
        Set<RunStop.Site> named = new LinkedHashSet<>();
        Set<RunStop.Site> shownAt = new LinkedHashSet<>();
        Map<RunStop.Site, Set<Enum<?>>> openAt = new LinkedHashMap<>();
        for (WhatIsShownOfAStop each : said) {
            Optional<RunStop.Site> step = runs.placed(each.at());
            if (step.isEmpty()) {
                out.add(new Unheld(Claim.A_STEP_WRITTEN_SOMEWHERE, each.toString()));
                continue;
            }
            named.add(step.get());
            switch (each) {
                case StepWhereARunMayStop stops -> {
                    shownAt.add(step.get());
                    shown(stops, step.get(), runs, out, notHeldTo);
                }
                case StepWhereAStopIsNotShown open -> {
                    Set<Enum<?>> why = openAt.computeIfAbsent(step.get(),
                            _ -> new LinkedHashSet<>());
                    open.notShown().forEach(one -> why.add(one.why()));
                    open.asks().forEach(one -> why.add(one.why()));
                }
            }
            heldTo[0] += everyRunStops(everyRunStopsOf(each), step.get(), runs, out, notHeldTo);
            heldTo[1] += keeping(keepingOf(each), step.get(), runs, out, notHeldTo);
        }
        Set<RunStop.Site> stoppedAt = new LinkedHashSet<>();
        for (Run run : runs.grid()) {
            said(run, named, out);
            run.stepToSay().ifPresent(stoppedAt::add);
        }
        Map<RunStop.Site, Set<Enum<?>>> notShown = new LinkedHashMap<>();
        for (RunStop.Site step : stoppedAt) {
            if (openAt.containsKey(step) && !shownAt.contains(step)) {
                notShown.put(step, openAt.get(step));
            }
        }
        Set<RunStop.Site> noneStops = new LinkedHashSet<>(openAt.keySet());
        noneStops.removeAll(stoppedAt);
        return new Held(out, notHeldTo, notShown, noneStops, heldTo[0], heldTo[1]);
    }

    /**
     * That a stop of {@code run} is at a step some finding names: the step it stopped at first,
     * or, where it stopped inside a call of the body, that call. Where the stop or the call says no
     * place, that is said whatever is named: a place not said is no place a finding is shown to
     * name.
     */
    private static void said(Run run, Set<RunStop.Site> named, List<Unheld> out) {
        if (run.stopped().isEmpty()) {
            return;
        }
        Optional<RunStop.Site> first = run.firstStopAt();
        if (first.isEmpty()) {
            out.add(new Unheld(Claim.EVERY_STOP_PLACED, run.in() + " stops where the code says no"
                    + " place: " + run.stopped()));
            return;
        }
        if (named.contains(first.get())) {
            return;
        }
        Optional<Optional<RunStop.Site>> call = run.endedInsideACall();
        if (call.isPresent() && call.get().isEmpty()) {
            out.add(new Unheld(Claim.EVERY_STOP_PLACED, run.in() + " stops inside a call the code"
                    + " says no place for: " + run.stopped()));
        } else if (call.isEmpty() || !named.contains(call.get().get())) {
            out.add(new Unheld(Claim.EVERY_STOP_SAID, run.in() + " stops at " + first.get()
                    + call.map(at -> " inside the call at " + at.get()).orElse("")
                    + ", a step nothing is said of: " + run.stopped()));
        }
    }

    /** Each run of a witness of a stop shown at {@code step} stops there first. */
    private static void shown(StepWhereARunMayStop stops, RunStop.Site step, Runs runs,
                              List<Unheld> out, List<String> notHeldTo) {
        for (AStopShown shown : stops.shown()) {
            Optional<List<Map<String, Object>>> inputs =
                    runs.completions(shown.at(), shown.structure());
            if (inputs.isEmpty()) {
                notHeldTo.add("a witness no input of these is built of: " + shown);
                continue;
            }
            for (Map<String, Object> in : inputs.get()) {
                Run run = runs.of(in);
                if (!run.endedAt(step)) {
                    out.add(new Unheld(Claim.A_STOP_SHOWN, shown.operation() + " shown at " + step
                            + ", and the run of " + in + " stops first at " + run.firstStopAt()
                            + ": " + run.stopped()));
                }
            }
        }
        for (AConstructionStopShown shown : stops.constructions()) {
            Optional<List<Map<String, Object>>> inputs = runs.completions(shown.at(), List.of());
            if (inputs.isEmpty()) {
                notHeldTo.add("a witness no input of these is built of: " + shown);
                continue;
            }
            for (Map<String, Object> in : inputs.get()) {
                Run run = runs.of(in);
                if (!(run.stopped().orElse(null) instanceof RunStop.AtAConstruction)
                        || !run.firstStopAt().equals(Optional.of(step))) {
                    out.add(new Unheld(Claim.A_STOP_SHOWN, "a construction shown at " + step
                            + ", and the run of " + in + " stops first at " + run.firstStopAt()
                            + ": " + run.stopped()));
                }
            }
        }
    }

    /** Every run of the grid inside the rows, getting to {@code step}, stops there. Answers how
     *  many of {@code stops} some run of the grid is about. */
    private static int everyRunStops(List<EveryRunStops> stops, RunStop.Site step, Runs runs,
                                     List<Unheld> out, List<String> notHeldTo) {
        int heldTo = 0;
        for (EveryRunStops each : stops) {
            boolean about = false;
            boolean weighed = true;
            for (Run run : runs.grid()) {
                Optional<Boolean> inside = inside(each.where(), run.in());
                if (inside.isEmpty()) {
                    notHeldTo.add("rows over what is no value at a place: " + each);
                    weighed = false;
                    break;
                }
                if (!inside.get() || !run.gotTo(step)) {
                    continue;
                }
                about = true;
                if (!run.endedAt(step)) {
                    out.add(new Unheld(Claim.EVERY_RUN_STOPS, "every run getting to " + step
                            + " in " + each + " stops there, and the run of " + run.in()
                            + " stops first at " + run.firstStopAt() + ": " + run.stopped()));
                }
            }
            heldTo += (about && weighed) ? 1 : 0;
        }
        return heldTo;
    }

    /** No run of the grid meeting the bounds stops at {@code step} past where a number stops.
     *  Answers one where some run of the grid is about what is kept, and none where none is or
     *  nothing is kept. */
    private static int keeping(Optional<WhatKeepsEveryRunGoing> kept, RunStop.Site step, Runs runs,
                               List<Unheld> out, List<String> notHeldTo) {
        if (kept.isEmpty()) {
            return 0;
        }
        boolean about = false;
        for (Run run : runs.grid()) {
            Optional<Boolean> meets = meets(kept.get().bounds(), run.in(), runs.input);
            if (meets.isEmpty()) {
                notHeldTo.add("bounds declared on what is no place of the input: "
                        + kept.get().bounds());
                return 0;
            }
            if (!meets.get() || !run.gotTo(step)) {
                continue;
            }
            about = true;
            if (run.endedAt(step)) {
                out.add(new Unheld(Claim.KEEPING, "no run within " + kept.get().bounds()
                        + " stops at " + step + ", and the run of " + run.in() + " does: "
                        + run.stopped()));
            }
        }
        return about ? 1 : 0;
    }

    /**
     * Whether {@code in} is within every one of {@code where}; none where one weighs what is not a
     * whole number at a place of the input or an element of a list at one, weighs elements of two
     * lists, or weighs a number by other than a whole number.
     *
     * <p>A form weighing the element of a list is within where every element is, the list holding
     * one: whichever element a step standing for every element is first applied to is then
     * within, so a run that gets to the step gets there inside them. A list some elements of which
     * are within and some not is no input this says is, and holds no claim to it.
     */
    private static Optional<Boolean> inside(List<EveryRunStops.Within> where,
                                            Map<String, Object> in) {
        boolean inside = true;
        for (EveryRunStops.Within within : where) {
            Map<String, BigInteger> weights = new LinkedHashMap<>();
            String list = null;
            for (Map.Entry<NumericTerm, ExactRatio> term : within.form().coefs().entrySet()) {
                BigInteger weight = term.getValue().wholeOrNull();
                if (weight == null || !(term.getKey() instanceof NumericTerm.ValueOf(
                        TermPath path))) {
                    return Optional.empty();
                }
                Optional<String> place = placeOf(path);
                Optional<String> elementOf = elementOf(path);
                if (place.isPresent() && in.get(place.get()) instanceof Long) {
                    weights.put(place.get(), weight);
                } else if (elementOf.isPresent() && (list == null || list.equals(elementOf.get()))
                        && in.get(elementOf.get()) instanceof List<?>) {
                    list = elementOf.get();
                    weights.put(list, weight);
                } else {
                    return Optional.empty();
                }
            }
            List<?> elements = list == null ? List.of(0L) : (List<?>) in.get(list);
            inside &= !elements.isEmpty();
            for (Object element : elements) {
                BigInteger sum = BigInteger.ZERO;
                for (Map.Entry<String, BigInteger> each : weights.entrySet()) {
                    Object value = each.getKey().equals(list) ? element : in.get(each.getKey());
                    sum = sum.add(each.getValue().multiply(BigInteger.valueOf((Long) value)));
                }
                inside &= (within.least() == null || sum.compareTo(within.least()) >= 0)
                        && (within.greatest() == null || sum.compareTo(within.greatest()) <= 0);
            }
        }
        return Optional.of(inside);
    }

    /** Whether {@code in} meets every one of {@code bounds}; none where one is declared on
     *  something other than a whole-number place of the input. */
    private static Optional<Boolean> meets(Set<ABoundThatKeepsEveryRunGoing> bounds,
                                           Map<String, Object> in, Input input) {
        boolean meets = true;
        for (ABoundThatKeepsEveryRunGoing bound : bounds) {
            Optional<String> place = fieldBounded(bound, input);
            if (place.isEmpty() || !(in.get(place.get()) instanceof Long value)) {
                return Optional.empty();
            }
            BigInteger number = BigInteger.valueOf(value);
            meets &= bound.atMost() ? number.compareTo(bound.at()) <= 0
                    : number.compareTo(bound.at()) >= 0;
        }
        return Optional.of(meets);
    }

    /** The place of {@code input} {@code bound} is declared on: a field of the data the
     *  behaviors take, named by the invariant; none where it is declared on anything else. */
    private static Optional<String> fieldBounded(ABoundThatKeepsEveryRunGoing bound, Input input) {
        if (bound.holder() instanceof ABoundThatKeepsEveryRunGoing.Holder.AData data
                && data.data().module().equals(input.module())
                && data.data().name().equals(input.data())
                && data.named().steps().size() == 1
                && input.values().containsKey(data.named().steps().getFirst())) {
            return Optional.of(data.named().steps().getFirst());
        }
        return Optional.empty();
    }

    private static List<EveryRunStops> everyRunStopsOf(WhatIsShownOfAStop each) {
        return switch (each) {
            case StepWhereARunMayStop it -> it.everyRunStops();
            case StepWhereAStopIsNotShown it -> it.everyRunStops();
        };
    }

    private static Optional<WhatKeepsEveryRunGoing> keepingOf(WhatIsShownOfAStop each) {
        return switch (each) {
            case StepWhereARunMayStop it -> it.keeping();
            case StepWhereAStopIsNotShown it -> it.keeping();
        };
    }

    /** The place of the input {@code path} is, where it is one field of the data the behaviors
     *  take; none where it reaches into one, an element of a list or a field of a record. */
    static Optional<String> placeOf(TermPath path) {
        return (path.steps().size() == 1
                && path.steps().getFirst() instanceof TermPath.Step.Field(String name))
                ? Optional.of(name) : Optional.empty();
    }

    /** The place of the input whose element {@code path} is, where it is the element of a list at
     *  one field of the data the behaviors take; none otherwise. */
    static Optional<String> elementOf(TermPath path) {
        return (path.steps().size() == 2
                && path.steps().getFirst() instanceof TermPath.Step.Field(String name)
                && path.steps().getLast() instanceof TermPath.Step.Element)
                ? Optional.of(name) : Optional.empty();
    }

    /** What the findings of {@code behavior} of {@code module} say of where its runs may stop. */
    static List<WhatIsShownOfAStop> saidOf(Compilation compiled, String module, String behavior) {
        return compiled.db().ask(new Adequacy.Divided(module, behavior)).value().stopsShown();
    }
}
