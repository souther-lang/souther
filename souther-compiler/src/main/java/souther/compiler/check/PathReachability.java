package souther.compiler.check;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.SeenConditionOutcome;
import souther.compiler.coverage.NumberingIdentity;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.diag.SourcePos;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.flow.WhyNoValueTakesTheArm;
import souther.compiler.flow.WhyRuledOut;
import souther.compiler.inputs.Admits;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.ValueDefinitions;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Unsettlement;
import souther.compiler.partition.WhatTheDeclarationsLeaveAnArm;
import souther.compiler.partition.WhereAClosureIsApplied;
import souther.compiler.types.ResolvedCase;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionBounds;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.reach.ValuesNamed;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.reach.ComparisonArrival;
import souther.compiler.reach.PathDecision;
import souther.compiler.reach.Proof;
import souther.compiler.reach.Reachability;
import souther.compiler.reach.Witness;
import souther.compiler.reach.WhatMayStopARun;
import souther.compiler.reach.WhyUnsettled;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.types.BindingId;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * What the model's own rules say arrives at each place in a behavior's body.
 *
 * <p>The reading the invariant-discharge check already makes, answered as a fact instead of
 * consumed as a step. That check threads what holds where it stands and returns at a place the
 * conditions cannot all hold — which is exactly the question every measure asks about an arm, and
 * every measure was answering it again from the declarations alone, with no way to know what the
 * guards above had established. Two guards on one position left the second one's departure owed a
 * row that nothing can write.
 *
 * <p>Held by {@link ControlPlace} and not by probe number. An arm answering {@code unreachable}
 * has no probe, and it is the arm a claim is about.
 *
 * <p><b>Only a proof excludes, and nothing here proves that something arrives.</b> A state the
 * domains found no contradiction in is a state they had nothing to say about, so this answers
 * {@link Reachability.Unsettled} there rather than {@link Reachability.Reachable} — what earns the
 * latter is a run, or a rule that settles the question completely, and neither is read here.
 *
 * <p>A place this walk did not get to is absent, which {@link Answers#at} reads as unsettled. That
 * is the fail-open direction and it is the one that costs nothing: an obligation stays owed and
 * nothing is reported.
 */
public final class PathReachability {

    /**
     * What arrives at each construct a line is drawn at — a comparison, or an application whose
     * answer states one — before it is taken either way, and where a row coming to it is recorded.
     *
     * <p>Its own value beside the places ({@link Answers#found}) because it is a fact of its own
     * and is read on its own. A line is dropped by what arrives at the construct, and the division
     * that drops it reads nothing about any arm or way out; handed the places as well, it would be
     * made again whenever a row went somewhere new, over arrivals that had not moved, and could ask
     * a place a question it has no business asking.
     *
     * @param numbering  which plan's constructs these are, or empty where no reading was made
     * @param arriving   what arrives at each, in the order the walk met them
     * @param recordedAt where a row coming to each is recorded, which is the plan's and is kept
     *                   here, asked of the plan where the reading was made, so that a run can be
     *                   read against it later with no plan in hand. A comparison's way out and an
     *                   application's answer are both recorded there, and a row recorded there
     *                   either way came to it
     * @param stopsBefore what a run arriving at each construct may have stopped at on the way for
     *                   what nothing here says, for each construct where it may — an operator or a
     *                   call worked out before it whose operands this reading does not hold to
     *                   where it answers ({@link PathCompletion.Past#mayStop}). What
     *                   arrives there is what has to hold for a run to get there, and a construct
     *                   here is one where that is not all that getting there takes
     */
    public record Arrivals(Optional<NumberingIdentity> numbering,
                           Map<ConstructOccurrence, ComparisonArrival> arriving,
                           Map<ConstructOccurrence, ConditionOutcomeSite> recordedAt,
                           Map<ConstructOccurrence, List<WhatMayStopARun>> stopsBefore) {

        /** No reading, which goes with any plan because it says nothing about one. */
        public static final Arrivals NONE =
                new Arrivals(Optional.empty(), Map.of(), Map.of(), Map.of());

        public Arrivals {
            if (numbering == null) {
                throw new IllegalArgumentException(
                        "a reading either was made under some numbering or was not made");
            }
            if (numbering.isEmpty() && !(arriving.isEmpty() && recordedAt.isEmpty()
                    && stopsBefore.isEmpty())) {
                throw new IllegalArgumentException("a reading that answered about "
                        + arriving.size() + " constructs was made under some numbering; they are"
                        + " of a plan and nothing here would say which");
            }
            arriving = Collections.unmodifiableMap(new LinkedHashMap<>(arriving));
            recordedAt = Collections.unmodifiableMap(new LinkedHashMap<>(recordedAt));
            Map<ConstructOccurrence, List<WhatMayStopARun>> stops = new LinkedHashMap<>();
            stopsBefore.forEach((construct, at) -> stops.put(construct, List.copyOf(at)));
            stopsBefore = Collections.unmodifiableMap(stops);
        }

        /**
         * What a run arriving at {@code at} may have stopped at on the way for what nothing here
         * says, each kind once — none where everything worked out on the way is held to where it
         * answers, and none where this reading was not made.
         */
        public List<WhatMayStopARun> stopsBefore(ConstructOccurrence at) {
            return stopsBefore.getOrDefault(at, List.of());
        }

        /** That the constructs {@code of} names are the ones this reading answered about — see
         *  {@link Answers#requireNumbering}, which holds the places to the same. */
        public void requireNumbering(NumberingIdentity of) {
            requireOf(numbering, of);
        }

        /**
         * What arrives at {@code at} — one construct a line is drawn at, before it is taken
         * either way.
         *
         * <p>An entry's absence reads as {@link ComparisonArrival.NoProjection}, which restricts
         * nothing. Two ways to have none, and one answer for both: this reading was never made at
         * all — the caller holds {@link #NONE}, which is what a reader of a construct outside a
         * measured body is given — or the walk fell over before finishing, since a walk that
         * finished is held to an entry per numbered comparison ({@link PathReachability#unanswered}).
         * A partial reading is owed the fail-open answer, the same one every other consumer of one
         * gets.
         *
         * <p>What is not among them is a construct this plan numbers no site for. There is no
         * occurrence to ask about then, and a caller that has one has it from the plan — asked with
         * something worked out another way, an absence here would be this reading and the plan
         * disagreeing, dressed as a fact about the model.
         */
        public ComparisonArrival arrivalAt(ConstructOccurrence at) {
            ComparisonArrival answer = arriving.get(at);
            return answer != null ? answer : new ComparisonArrival.NoProjection();
        }

        /** The constructs proven to be arrived at by nothing that a row is recorded coming to,
         *  either way, in {@code seen}. */
        Set<ConstructOccurrence> shownWrongBy(Set<SeenConditionOutcome> seen) {
            Set<ConstructOccurrence> out = new LinkedHashSet<>();
            recordedAt.forEach((construct, site) -> {
                if (arriving.get(construct) instanceof ComparisonArrival.NothingArrives
                        && (seen.contains(new SeenConditionOutcome(site, true))
                                || seen.contains(new SeenConditionOutcome(site, false)))) {
                    out.add(construct);
                }
            });
            return out;
        }

        /** These, with what arrives at each of {@code takenBack} answered as what restricts
         *  nothing: a row came, and which values did is not what the run says. */
        Arrivals takingBack(Set<ConstructOccurrence> takenBack) {
            if (takenBack.isEmpty()) {
                return this;
            }
            Map<ConstructOccurrence, ComparisonArrival> out = new LinkedHashMap<>(arriving);
            takenBack.forEach(construct -> out.put(construct, new ComparisonArrival.NoProjection()));
            return new Arrivals(numbering, out, recordedAt, stopsBefore);
        }
    }

    /**
     * The one check a reading and a plan are held to each other by, for the places and the
     * constructs alike.
     */
    private static void requireOf(Optional<NumberingIdentity> numbering, NumberingIdentity of) {
        if (numbering.isPresent() && !numbering.get().equals(of)) {
            throw new IllegalArgumentException("this reading was made under " + numbering.get()
                    + " and is being read against " + of
                    + "; what one plan's reading says about another's places is nothing, and"
                    + " answering it would report every place of a body as one nothing"
                    + " reached");
        }
    }

    /**
     * What was found, and what a place nothing was found about comes to.
     *
     * @param numbering which plan's places these are filed under, or empty where no reading was
     *                  made at all. Not read off the entries: a reading of a body with nothing to
     *                  say about it is a reading and answers for that plan, while what a caller
     *                  holds where a module's reading could not be made is no reading and answers
     *                  for none. The two are the same map and are not the same fact
     * @param arrivals  what arrives at each construct a line is drawn at, under the same numbering
     */
    public record Answers(Optional<NumberingIdentity> numbering,
                          Map<ControlPlace, Reachability> found,
                          Arrivals arrivals) {

        /** No reading, which every consumer takes the way it takes a place nothing was found
         *  about, and which goes with any plan because it says nothing about one. */
        public static final Answers NONE = new Answers(Optional.empty(), Map.of(), Arrivals.NONE);

        public Answers {
            if (numbering == null) {
                throw new IllegalArgumentException(
                        "a reading either was made under some numbering or was not made");
            }
            if (numbering.isEmpty() && !found.isEmpty()) {
                throw new IllegalArgumentException(
                        "a reading that answered about " + found.size() + " places was made under"
                                + " some numbering; its places are of a plan and nothing here"
                                + " would say which");
            }
            if (!numbering.equals(arrivals.numbering())) {
                throw new IllegalArgumentException("the places were read under " + numbering
                        + " and what arrives at the constructs under " + arrivals.numbering()
                        + "; one reading of one body is of one plan");
            }
            // The order the walk found them in. `Map.copyOf` is unordered and its iteration is
            // salted per run, so the warnings read off this came out in a different order on every
            // JVM — a diagnostic whose place in the output is not a function of the source.
            found = Collections.unmodifiableMap(new LinkedHashMap<>(found));
        }

        /**
         * That the places {@code of} names are the places this reading answered about.
         *
         * <p><b>Said once, where a plan and a reading of it are put together, and not at each
         * lookup.</b> Absent here reads as unsettled and that is the right answer for a place the
         * walk did not get to — and the same answer for a place of another module's plan, which is
         * not an answer about this reading at all. A place cannot be asked which plan it is of: an
         * arm no run can be recorded in carries no numbering, and giving it one would put the
         * plan's own address back inside the identity. So the pairing is what is checked, and it is
         * checked where the two halves meet.
         *
         * <p>Beside {@code AlignedObservation}, which refuses a place of another numbering put to a
         * recording. Both are read back under a numbering, and now both say so.
         *
         * <p>{@link #NONE} goes with any plan. What a caller holds where no reading was made says
         * nothing about any module's places, and every consumer already treats it the way it treats
         * a place nothing was found about.
         */
        public void requireNumbering(NumberingIdentity of) {
            requireOf(numbering, of);
        }

        /**
         * What arrives at {@code where}.
         *
         * <p>A place this reading has nothing filed under is one the walk did not get to, which is
         * an answer and not a gap: it is {@link WhyUnsettled.TheWalkDidNotReachIt}, and every
         * consumer treats it as it treats any other unsettled place. Which is why the reading and
         * the plan are held to being one another's first ({@link #requireNumbering}).
         *
         * <p><b>Asked with the place and never with an address of one.</b> A probe says where a run
         * through an arm is recorded, and which arm that is is the numbering's answer, given where
         * the number was handed out. Asked here, it would be that correspondence worked out again
         * by search — over the entries of one reading, which knows of no numbering and could not
         * tell two arms answering to one probe apart if a walk ever made them.
         */
        public Reachability at(ControlPlace where) {
            Reachability answer = found.get(where);
            return answer != null ? answer
                    : new Reachability.Unsettled(WhyUnsettled.theWalkDidNotReachIt());
        }

        /**
         * These answers with what the rows actually did taken in, and the proofs they took back.
         *
         * <p>A row that went through an arm went through it. So a run is a witness — the plainest
         * of them — and it settles an arm this reading had proven nothing arrives at: what happened
         * happened, and the proof was wrong rather than the row. Both come out of one act because
         * neither is derivable from the other afterwards: the corrected answers no longer say which
         * arms were corrected, and the corrections do not say what everything else came to.
         *
         * <p>A condition a row saw come out one way came out that way, by the same argument. Both
         * kinds of place are corrected here, in one act, because every reader of these answers
         * reads them corrected: a measure counting arms and one excluding a rule because a
         * comparison never comes out its way would otherwise stand on two different accounts of
         * what the rows did.
         *
         * <p>And a row that came to a construct a line is drawn at arrived at it. A row seen
         * bringing a comparison out either way — or an application answering either way — shows
         * wrong a proof that nothing arrives there, and what arrives is answered then with what
         * restricts nothing ({@link ComparisonArrival.NoProjection}): the run says a row came, and
         * not which values did. Asked of the arrivals where they say such a row is recorded
         * ({@link Arrivals#recordedAt}), and not of the places above, which hold no application.
         *
         * <p>Every place is held to one rule — seen, and proven unreachable, is a proof shown wrong
         * — and what that weakens is each measure's to say by what it rests on, not this reading's.
         *
         * @param lit  the probes a row was recorded at, which are places of the numbering this
         *             reading was made under. A probe of another is one no arm here answers to, so
         *             the run would correct nothing and every proof would stand — the same answer
         *             as a run that went nowhere
         * @param seen the ways a row saw a condition come out, of the same numbering
         */
        public AsRun asRunWith(Set<ArmProbe> lit, Set<SeenConditionOutcome> seen) {
            lit.forEach(probe -> requireNumbering(probe.numbering()));
            seen.forEach(outcome -> requireNumbering(outcome.at().numbering()));
            Map<ControlPlace, Reachability> out = new LinkedHashMap<>(found);
            Set<ControlPlace> places = new LinkedHashSet<>();
            found.forEach((where, said) -> {
                Optional<Witness> ran = switch (where) {
                    case ControlPlace.Arm arm ->
                            arm.probe().filter(lit::contains).map(Witness::aRunWentThrough);
                    case ControlPlace.Outcome outcome ->
                            seen.contains(new SeenConditionOutcome(outcome.at(), outcome.held()))
                                    ? Optional.of(Witness.aRunWentThrough(outcome.at()))
                                    : Optional.empty();
                };
                if (ran.isEmpty()) {
                    return;
                }
                if (said instanceof Reachability.Unreachable) {
                    places.add(where);
                }
                out.put(where, new Reachability.Reachable(ran.get()));
            });
            Set<ConstructOccurrence> emptyArrivals = arrivals.shownWrongBy(seen);
            if (places.isEmpty() && emptyArrivals.isEmpty()) {
                return new AsRun(new Answers(numbering, out, arrivals), Contradictions.NONE);
            }
            return new AsRun(new Answers(numbering, out, arrivals.takingBack(emptyArrivals)),
                    new Contradictions(places, emptyArrivals));
        }

        /**
         * What arrives once the rows have run, and where this reading was shown wrong.
         *
         * @param answers      what arrives, with every proof a row went against taken back
         * @param contradicted the proofs a row went against. Nothing about the model is wrong then
         *                     — this reading is — and a measure that rested on one says so rather
         *                     than quietly counting what it had left out
         */
        public record AsRun(Answers answers, Contradictions contradicted) {

            public AsRun {
                Objects.requireNonNull(answers, "a run is a run of some reading");
                Objects.requireNonNull(contradicted, "a run shows some proofs wrong, or none");
            }
        }

        /**
         * The proofs of one reading a row went against, held where the reading is and once.
         *
         * <p>Two kinds, because they are two propositions. That nothing comes out of a comparison
         * one way is about a place ({@link ControlPlace.Outcome}), as nothing arriving at an arm is;
         * that nothing arrives at a construct a line is drawn at is about the construct
         * ({@link Arrivals}), and either way out of a comparison may be rightly proven while that
         * is wrong.
         *
         * <p>Only what a run is recorded at. An arm answering {@code unreachable} has no probe, so a
         * row reaching one is never here — reaching it is an error of its own, E1911 — and what an
         * author claimed unreachable is judged from the model before any row runs, which this
         * leaves as it was.
         *
         * @param places        arms and comparison outcomes proven unreachable that a row went
         *                      through
         * @param emptyArrivals comparisons and applications proven to be arrived at by nothing
         *                      that a row came to
         */
        public record Contradictions(Set<ControlPlace> places,
                                     Set<ConstructOccurrence> emptyArrivals) {

            /** No proof gone against. */
            public static final Contradictions NONE = new Contradictions(Set.of(), Set.of());

            public Contradictions {
                // The order the reading found them in, which is the order a report says them in.
                places = Collections.unmodifiableSet(new LinkedHashSet<>(places));
                emptyArrivals = Collections.unmodifiableSet(new LinkedHashSet<>(emptyArrivals));
            }

            /** Whether a row went against no proof at all. */
            public boolean isEmpty() {
                return places.isEmpty() && emptyArrivals.isEmpty();
            }
        }

        /** Whether this reading proved nothing arrives anywhere, which is what a walk that would
         *  only ever answer "keep everything" can skip on. */
        public boolean provesNothingUnreached() {
            return found.values().stream().noneMatch(Reachability.Unreachable.class::isInstance);
        }
    }

    /**
     * The places of one behavior's body, read against what its declared inputs guarantee.
     *
     * <p>The bindings are the implementation's own and the types are the declaration's, paired by
     * position and stopping at the business parameters — which is the rule the check that types the
     * body reads them by, asked here rather than worked out a second way. A trailing parameter
     * stands for a behavior this one depends on and guarantees nothing about a value.
     *
     * <p><b>The reading is required.</b> What a caller has where a module's could not be made is no
     * reading, and a walk of a body against one made up says about this compilation having stopped
     * what it would say about the model. A caller without one measures nothing here.
     */
    public static Answers of(Core body, SpecImplementation.Implemented implemented,
                             CoverageSites.Plan plan, InputReading read,
                             RuleReadingContext ruleReading, MeaningsOfABody meanings,
                             ElementBindings elements, ValueDefinitions values) {
        Objects.requireNonNull(read, "a reachability reading is made against an input that was read");
        if (implemented == null) {
            return Answers.NONE;
        }
        // Which binder each declared input arrives in, asked of the reading that divides an
        // implementation's parameters. A behavior takes the behaviors it depends on beside its
        // inputs, so which of the binders are the inputs is that reading's and not a prefix
        // measured here.
        Scope params = Scope.NONE;
        for (SpecImplementation.ParameterBinding.AnInput input : implemented.declaredInputs()) {
            params = params.with(input.written().binder(),
                    TypeOps.successType(input.declared().type()));
        }
        return of(body, params, plan, read, ruleReading, meanings, elements, values);
    }

    /**
     * The same, told the bindings outright.
     *
     * <p>Fail-open throughout. A condition of a shape the rules have no word for narrows nothing,
     * so the arms under it come out unsettled rather than proven either way; a walk that falls over
     * answers about what it had reached and no more.
     *
     * <p>What a condition of the model states is {@code meanings}' — read once, off the tree where
     * the language's operations stand — and is what a path takes in where it passes one. A
     * condition inside a copy of one of the language's operations is no condition of the model:
     * the path goes on through it and takes nothing in.
     *
     * <p>A value the body builds is a call of the value's method in the tree this walks, and what
     * the value is defined as is in {@code values}, held in the tree an analysis reads. Both
     * readings this walk makes — of what its conditions state, and of the input its comparisons are
     * about — read a name given such a call as that definition, where a definition is read and
     * nothing of this body is in force — so a fork on a value the module declares is settled as one
     * on the value written out, and nothing of the other representation is read under this body's
     * names.
     */
    public static Answers of(Core body, Scope params, CoverageSites.Plan plan,
                             InputReading reading, RuleReadingContext ruleReading,
                             MeaningsOfABody meanings, ElementBindings elements,
                             ValueDefinitions values) {
        Objects.requireNonNull(reading,
                "a reachability reading is made against an input that was read");
        if (body == null) {
            return Answers.NONE;
        }
        InputDomain read = reading.domain();
        PathEngine engine = new PathEngine(ruleReading, Map.of(), Terms.Of.THE_TREE_THAT_RUNS,
                values.templates());
        Map<ControlPlace, Reachability> out = new LinkedHashMap<>();
        Map<ConstructOccurrence,
                souther.compiler.reach.ComparisonArrival> arriving = new LinkedHashMap<>();
        PathEngine.Entered in = engine.nothingEntered();
        for (Map.Entry<BindingId, Scope.Binding> p : params.bindings().entrySet()) {
            in = engine.enter(new Core.Read(p.getValue().name(), p.getKey(),
                    p.getValue().type(), body.pos()), in.known(), in.at());
        }
        Map<String, BindingId> parameters = new LinkedHashMap<>();
        read.parameterReads().forEach((binding, name) -> parameters.put(name, binding));
        PathReachability walker =
                new PathReachability(engine, plan, reading, ruleReading.source().symbols(),
                        ruleReading.source().newtypes(), out,
                        arriving, meanings, new MeaningAssumptions.InputPlaces(parameters,
                                path -> read.typeAt(path, ruleReading.source()), Map.of(),
                                Map.of()));
        walker.entry = in.known();
        walker.entered = in.at();
        walker.walk(body, Walked.entering(in.known()), in.at(),
                        InputReads.ofParameters(read.parameterReads(),
                                read.declared(ruleReading.source()), elements, values,
                                read.dependencies()));
        // A walk that ran to the end and made none of the answers it is written to produce. Its own
        // limit and said as one: the analysis this borrows is open about what it reads, so a
        // comparison it reached and settled nothing about leaves the obligation standing. A failure
        // of the walk itself is not this and is not caught — it is this compiler's.
        Optional<String> unmade = unanswered(body, plan, out, arriving);
        if (unmade.isPresent()) {
            InvariantChecker.gaveUp("reachability",
                    WhatTheCheckCannotRead.theWalkLeftAnAnswerUnmade(unmade.get()));
        }
        // Where a row coming to each of them is recorded, asked of the plan while it is in hand: a
        // run read against this reading later has the recordings and no plan.
        Map<ConstructOccurrence, ConditionOutcomeSite> recordedAt = new LinkedHashMap<>();
        arriving.keySet().forEach(construct -> plan.outcomeOf(construct, true)
                .ifPresent(way -> recordedAt.put(construct, way.at())));
        Optional<NumberingIdentity> numbering = Optional.of(plan.identity());
        return new Answers(numbering, out,
                new Arrivals(numbering, arriving, recordedAt, walker.stopsBefore));
    }

    /**
     * Which comparison {@code node} is, where this plan instruments it, or null.
     *
     * <p>Two questions and two answers, asked of whichever holds each. Which comparison a node is,
     * the catalog says, for every comparison the bodies hold; whether a run through it is written
     * down anywhere, the plan says, for the ones it numbered. What is filed under one of these is
     * about a place a run can be observed at, so both have to answer.
     */
    private static ConstructOccurrence numbered(Core.Binary node, CoverageSites.Plan plan) {
        return plan.comparisons().occurrenceAt(node).filter(plan::instruments).orElse(null);
    }

    /**
     * That the walk answered for every comparison the plan numbered in this body.
     *
     * <p>What the reading owes, checked rather than left to the shape of the walk. Absent and
     * unsettled are the same answer to every reader below — a line is dropped only by a proof — so a
     * comparison the walk never reached is a claim nobody can find missing. The walk stops at a
     * place nothing arrives at, and a node it stops at can stand over comparisons: which ones
     * depends on how a condition was bracketed, which is not a thing to keep in step by reading.
     *
     * <p>Only where the walk finished, and reported rather than thrown. This reading is fail-open
     * by contract — what it does when the analysis it borrows falls over is answer about what it
     * reached and no more — so a walk that missed one says less, the way it does for everything
     * else it cannot settle. Thrown from here it would abort a compile on one path
     * ({@code Adequacy.PathReached}) and come back as a build with no classes and no reason on
     * another ({@code Output.Evaluated} takes an absent answer for a failure).
     *
     * @return what went unanswered, or empty where nothing did
     */
    private static Optional<String> unanswered(
            Core body, CoverageSites.Plan plan, Map<ControlPlace, Reachability> out,
            Map<ConstructOccurrence,
                    souther.compiler.reach.ComparisonArrival> arriving) {
        // Which comparison this is, and only where the plan numbers one there: what is owed is
        // owed for the places a run could be recorded at, and a node that is no comparison of this
        // plan is a node there was nothing to answer about.
        if (body instanceof Core.Binary comparison) {
            Optional<String> here = unansweredAt(comparison, plan, out, arriving);
            if (here.isPresent()) {
                return here;
            }
        }
        List<String> missed = new ArrayList<>();
        Core.forEachChild(body, child ->
                unanswered(child, plan, out, arriving).ifPresent(missed::add));
        return missed.isEmpty() ? Optional.empty()
                : Optional.of(missed.get(0));
    }

    /**
     * What one comparison of the body was owed and did not get, or empty where it was owed nothing.
     *
     * <p>Owed only where the plan numbers one here. A node that is no comparison of this plan is a
     * place no run is recorded at, so there was never an answer for the walk to have missed.
     */
    private static Optional<String> unansweredAt(
            Core.Binary comparison, CoverageSites.Plan plan,
            Map<ControlPlace, Reachability> out,
            Map<ConstructOccurrence,
                    souther.compiler.reach.ComparisonArrival> arriving) {
        ConstructOccurrence which = numbered(comparison, plan);
        if (which == null) {
            return Optional.empty();
        }
        for (boolean result : new boolean[] {true, false}) {
            ControlPlace where = plan.outcomeOf(which, result).orElse(null);
            if (where != null && !out.containsKey(where)) {
                return Optional.of(
                        "this reading answered for no run through " + comparison.op()
                                + " at " + comparison.pos() + " coming out " + result
                                + "; the plan numbered it and a reader below cannot tell an "
                                + "answer that was never made from one that settled nothing");
            }
        }
        // And the arrival beside the outcomes: filed with them or not at all, and a finished walk
        // owes it for the same reason it owes them — a reader below reads an absence as the answer
        // that restricts nothing, so only an audit here can tell the two apart.
        if (!arriving.containsKey(which)) {
            return Optional.of(
                    "this reading said nothing about what arrives at " + comparison.op()
                            + " at " + comparison.pos()
                            + "; the plan numbered it and a reader below cannot tell an answer"
                            + " that was never made from one that restricts nothing");
        }
        return Optional.empty();
    }

    private final PathEngine engine;
    /** What a run past each evaluation holds, read as the invariant check reads it. */
    private final PathCompletion completion;
    private final CoverageSites.Plan plan;
    /** What the declarations leave each position, which is what a {@code match} arm is held
     *  against. A condition narrows a path; a case is refused or left by the rules themselves. */
    private final InputDomain read;
    /** The same input with what its rules leave the numbers there, which is what an arm is asked
     *  of ({@link WhatTheDeclarationsLeaveAnArm}) — the one reading {@code NumberWays} asks it of
     *  too, so the two cannot answer about different inputs. */
    private final InputReading reading;
    private final Symbols symbols;

    /** Which declarations wear one value, which is what says whether reading a field reaches
     *  somewhere else ({@link Location#isStep}). */
    private final DeclarationNewtypes newtypes;
    private final Map<ControlPlace, Reachability> out;
    private final Map<ConstructOccurrence,
            souther.compiler.reach.ComparisonArrival> arriving;
    /** Where a run arriving at each construct may have stopped on the way for what nothing here
     *  says ({@link #mayStopBefore}), for the ones where it may. */
    private final Map<ConstructOccurrence, List<WhatMayStopARun>> stopsBefore =
            new LinkedHashMap<>();
    /**
     * What holds where the body begins: the inputs entered and seeded, and no condition taken.
     *
     * <p>Kept so a proof can say which of two things contradicts a branch. A condition that leaves
     * nothing against this alone is one the declarations rule out wherever it stands, and an author
     * told that the conditions on the way cannot all hold would go looking at the guards above for
     * something that is not there.
     */
    private Known entry;
    private Denotations entered = Denotations.none();
    /** What each condition of the model this body is states, read off the tree its operations
     *  stand in. */
    private final MeaningsOfABody meanings;
    /** Where the positions those statements name stand in this tree. */
    private final MeaningAssumptions.InputPlaces places;

    private PathReachability(PathEngine engine, CoverageSites.Plan plan, InputReading reading,
                             Symbols symbols, DeclarationNewtypes newtypes,
                             Map<ControlPlace, Reachability> out,
                             Map<ConstructOccurrence,
                                     souther.compiler.reach.ComparisonArrival> arriving,
                             MeaningsOfABody meanings, MeaningAssumptions.InputPlaces places) {
        this.engine = engine;
        this.completion = new PathCompletion(engine.terms(), engine.predicates());
        this.entry = engine.nothingKnown();
        this.plan = plan;
        // Here as well as at the ways in, so that nothing inside this class is written against a
        // reading that might not be one.
        this.reading = Objects.requireNonNull(reading);
        this.read = reading.domain();
        this.symbols = symbols;
        this.newtypes = newtypes;
        this.out = out;
        this.arriving = arriving;
        this.meanings = Objects.requireNonNull(meanings);
        this.places = places;
    }

    /**
     * What {@code k} comes to once {@code cond} — {@code part} of the construct {@code at} is one
     * of — comes out {@code positive}.
     *
     * <p>What a condition of the model states is read off {@link #meanings}. One inside a copy of
     * one of the language's operations is no rule of the model, so nothing is filed for it, but it
     * is what the path runs through and is read as it stands here. One the reading of the model has nothing filed for is read as it stands here.
     */
    private Predicates.Assumed assuming(ConstructOccurrence at, MeaningsOfABody.Part.Asked part,
                                        Core cond, Known k, Denotations in, InputReads reads,
                                        boolean positive) {
        Optional<ModelOccurrence> construct = ModelOccurrence.statedAt(at);
        if (construct.isEmpty()) {
            return engine.assuming(cond, k, in, positive);
        }
        MeaningsOfABody.Site site = new MeaningsOfABody.Site(construct.get(), part);
        Optional<Proposition> stated = meanings.at(site);
        if (stated.isPresent()) {
            return engine.assuming(stated.get(), cond, k, in, positive,
                    readBy(cond, reads));
        }
        // A body with no analysis to read it off has its conditions read as they stand here,
        // which is the one reading such a body has. A body that has one and files nothing at a
        // site takes nothing in there, for the reason nothing is filed: what its conditions mean
        // is not read twice.
        return meanings == MeaningsOfABody.NONE ? engine.assuming(cond, k, in, positive)
                : new Predicates.Assumed(k, false, false, List.of(
                        new WhyNotTaken.MeaningUnread(meanings.whyNothingAt(site))));
    }

    /**
     * The places of {@code cond}: the expression that reads each position of the input, where
     * {@code reads} places one, and the expression that is each place in an answer a dependency
     * gave — what a proposition about either is about, in this tree.
     *
     * <p>Only what is read where the condition stands. Under a binding the condition makes, a name
     * is one the bindings in force here say nothing of, so nothing below one is taken.
     */
    private MeaningAssumptions.InputPlaces readBy(Core cond, InputReads reads) {
        Map<TermPath, Core> positions = new HashMap<>();
        Map<MeaningAssumptions.AnswerPlace, Core> answers = new HashMap<>();
        gatherPlaces(cond, reads, positions, answers);
        return places.readBy(positions, answers);
    }

    private void gatherPlaces(Core standing, InputReads reads, Map<TermPath, Core> positions,
                              Map<MeaningAssumptions.AnswerPlace, Core> answers) {
        Core e = Core.withoutStanding(standing);
        for (Core each : Core.subexpressionsAt(e)) {
            if (reads.pathOf(each, newtypes) instanceof PathResolution.At(TermPath at)) {
                positions.putIfAbsent(at, each);
            } else if (reads.answerAt(each, symbols, newtypes) instanceof InputReads.AnAnswerAt(
                    var evaluation, var _, var _, var steps)) {
                answers.putIfAbsent(new MeaningAssumptions.AnswerPlace(evaluation, steps), each);
            }
        }
        if (e instanceof Core.LetIn || e instanceof Core.Block || e instanceof Core.Match
                || e instanceof Core.IfConstructed) {
            return;
        }
        Core.forEachChild(e, child -> gatherPlaces(child, reads, positions, answers));
    }

    /**
     * Reads {@code e} under what holds where it stands.
     *
     * <p>{@code decided} is the conditions taken in on the way here, in the order they were
     * assumed. Carried rather than recovered from where a place sits, because what a proof is
     * allowed to name is what the domains were actually given: a condition of a shape nothing could
     * take in narrowed nothing and is not on the list.
     *
     * <p>{@code mayStop} is what, worked out on the way here, may stop a run on operands nothing
     * here says ({@link PathCompletion.Past#mayStop}): what holds here is what has to
     * hold for a run to get here, and no more than that.
     */
    private Walked walk(Core e, Walked here, Denotations at, InputReads reads) {
        if (e == null) {
            return here;
        }
        Known k = here.known();
        if (k.reachesNothing()) {
            // Nothing stands here, so nothing below is a place anything arrives at either. Where an
            // arm on the way made it so, the arms under this are left absent, which reads as
            // unsettled: that arm was answered where it was entered, and saying it again at every
            // fork inside would be the same finding several times over. Where something worked out
            // made it so, no arm was, and the first fork past it is filed for that.
            //
            // The comparisons are not. What this reading owes is one answer per comparison the plan
            // numbered, and a comparison nothing arrives at is exactly a comparison nothing arrives
            // at — so the walk goes on for those and stops for everything else.
            unreached(e, here, at, reads);
            return here;
        }
        Walked operands = switch (e) {
            // A short circuit runs its right side only where the left settled nothing, so the two
            // sides do not stand under the same conditions. Threaded here rather than in a walk of
            // its own over a fork's condition: a chain is a chain wherever it is written, and one
            // read only under the fork it was written into left the same operators unread a line
            // above.
            case Core.Binary binary when binary.op().stopsWhenItsAnswerIsSettled() ->
                    shortCircuitOperands(binary, here, at, reads).completed();
            case Core.If iff -> {
                Exits exits = exitsOf(iff.cond(), here, at, reads);
                Walked cond = exits.completed();
                ControlPlace.Arm[] arms = plan.armsOf(iff);
                if (cond.known().reachesNothing()) {
                    // No run gets past the condition, so neither arm is entered. An arm the
                    // condition shuts where the fork stands is proven by the condition, as it is
                    // anywhere; the other by what the way to it answered nothing at. What is inside
                    // both is a place nothing arrives at.
                    Optional<Proof> noRunPast = cond.whyNothingArrives();
                    enterArm(arms, 0, iff, iff.then(), here, noRunPast, at, reads, true);
                    enterArm(arms, 1, iff, iff.els(), here, noRunPast, at, reads, false);
                    yield cond;
                }
                Walked then = enterArm(arms, 0, iff, iff.then(), exits.whenTrue(), Optional.empty(),
                        at, reads, true);
                Walked els = enterArm(arms, 1, iff, iff.els(), exits.whenFalse(), Optional.empty(),
                        at, reads, false);
                yield leaving(cond, List.of(then, els));
            }
            case Core.IfConstructed ic -> {
                // The construction's own arguments, then the arms. Reaching the success branch is
                // the construction having held, so its binding carries what the type guarantees —
                // which is the whole of what a guard inside that branch has to read against. Each
                // departure stands where nothing was built, so none is entered with any of it.
                //
                // One decision entered in both environments: what the binder denotes and which
                // position of the input it is are two readings of the same name, and a `then` that
                // entered it in one of them only would be read with the name meaning two things.
                Walked given = here;
                for (Core.FieldValue value : ic.construct().values()) {
                    given = walk(value.value(), given, at, reads);
                }
                Choice.Decides.ItWasBuilt held = Choice.Decides.ofBuilt(ic);
                PathEngine.Entered built = engine.enteringBuilt(held, given.known(), at);
                List<Walked> ways = new ArrayList<>();
                ways.add(walk(ic.then(), given.enteringAWay(built.known(), given.decided()),
                        built.at(), reads.choosing(held, symbols, newtypes)));
                for (Core.ElseArm arm : ic.els()) {
                    ways.add(walk(arm.body(), given.enteringAWay(given.known(), given.decided()),
                            at, reads.choosing(Choice.Decides.ofDeparture(ic, arm), symbols,
                                    newtypes)));
                }
                // No run gets past the arguments where they leave nothing, and then why is theirs
                // and not the ways'.
                if (given.known().reachesNothing()) {
                    given.whyNothingArrives().ifPresent(why -> noneEnters(plan.armsOf(ic), why));
                    yield given;
                }
                yield leaving(given, ways);
            }
            case Core.LetIn li -> {
                Walked value = walk(li.value(), here, at, reads);
                PathEngine.Entered in = engine.bindLet(li, value.known(), at);
                // Inside what the `let` binds, so an arm of an expanded helper is read against the
                // position the call handed it. A binding is not a fork, so what stands above the
                // body is what stood above the binding.
                yield walk(li.body(), value.at(in.known(), value.decided()), in.at(),
                        reads.entering(new ScopeStep.Let(li), symbols, newtypes));
            }
            case Core.Match match -> {
                Walked scrutinee = walk(match.scrutinee(), here, at, reads);
                Known before = scrutinee.known();
                if (before.reachesNothing()) {
                    // No run gets past the value matched on, so no arm is entered. An arm the
                    // rules shut where the match stands is proven by the rules, as it is anywhere;
                    // the others by what the way to them answered nothing at. What is inside each
                    // is a place nothing arrives at.
                    cases(match, k, at, reads, here.decided(), false);
                    scrutinee.whyNothingArrives()
                            .ifPresent(why -> noneEnters(plan.armsOf(match), why));
                    for (Core.Case arm : match.cases()) {
                        PathEngine.Entered in =
                                engine.enteringArm(arm, match.scrutinee(), before, at);
                        walk(arm.body(), scrutinee.enteringAWay(in.known(), scrutinee.decided()),
                                in.at(), reads.choosing(Choice.Decides.ofCase(match, arm), symbols,
                                        newtypes));
                    }
                    yield scrutinee;
                }
                List<PathDecision> on = scrutinee.decided();
                cases(match, before, at, reads, on, scrutinee.nothingAbove());
                // The scrutinee once and then the arms, written out rather than left to the generic
                // walk. A `Match`'s children are its scrutinee as well as its arm bodies, so
                // walking them all reads the scrutinee a second time — under a fork this time,
                // which takes back what was answered about anything in it.
                //
                // Each arm binds a value of the case it matched, which is a location holding
                // whatever that type guarantees: an arm of `| Paid p ->` reads `p`'s invariant, and
                // a guard inside it settles against that. Entering it is how the arm gets it, the
                // same act a parameter gets it by.
                //
                // Under an arm, this fork stands above whatever is inside it. Which arm was taken
                // is recorded as a decision where taking it settled which cases the value matched
                // may be, since a fork further in on the same value is read under that.
                List<Walked> ways = new ArrayList<>();
                for (Core.Case arm : match.cases()) {
                    PathEngine.Entered in = engine.enteringArm(arm, match.scrutinee(), before, at);
                    // And the name the arm binds stands for the scrutinee's position narrowed to
                    // the case it selects, which is where a comparison written inside the arm draws
                    // its line.
                    ways.add(walk(arm.body(), scrutinee.enteringAWay(in.known(),
                                    taking(on, arm, !in.known().cases().equals(before.cases()))),
                            in.at(),
                            reads.choosing(Choice.Decides.ofCase(match, arm), symbols, newtypes)));
                }
                yield leaving(scrutinee, ways);
            }
            case Core.Block block -> {
                // A closure operations apply over containers of the input runs only where one of
                // them holds something, which is what every reader entering it takes in. Where what
                // holds on the way here leaves that nothing, no run applies it and nothing in it is
                // reached — each arm in it for that reason, since no condition between the closure
                // and the arm is what shuts it. And something stands above what is in it, so no
                // witness is read off the rules alone there.
                Optional<WhereAClosureIsApplied> applied = WhereAClosureIsApplied.of(
                        reads.containersAppliedOver(block), reading);
                Known inside = applied.isEmpty() ? k
                        : engine.holding(applied.get().holdingSomething(), k, at, places).known();
                WhyNone why = WhyNone.BY_THE_WAY;
                if (inside.reachesNothing()) {
                    Proof none = Proof.itsClosureIsAppliedToNothing(
                            applied.orElseThrow().containers().stream()
                                    .map(TermPath::toString).toList(), here.decided());
                    appliedToNothing(block.body(), none);
                    why = new WhyNone.Because(none);
                }
                Walked body = walk(block.body(), new Walked(inside, here.decided(),
                                here.mayStop(), here.nothingAbove() && applied.isEmpty(), true,
                                why, inside.reachesNothing()), at,
                        reads.entering(new ScopeStep.Block(block), symbols, newtypes));
                // Making the function value runs nothing of its body, so nothing it holds is
                // carried on. What stopped a run in it is: the call that applies it is worked out
                // before what follows, and no state here holds where each application got past.
                yield inside.reachesNothing() ? here : here.pastAnApplicationOf(body);
            }
            // Every other node evaluates its parts whichever run it is on, one after another and
            // each under what the one before it left — so a run that stopped in one of them is no
            // run reaching the next.
            default -> {
                Walked part = here;
                for (Evaluated.Step step : Evaluated.inOrder(e)) {
                    part = walk(step.expression(), part, at,
                            reads.entering(ScopeStep.SAME, symbols, newtypes));
                }
                yield part;
            }
        };
        return pastOperands(e, operands, at, reads);
    }

    /**
     * What a run holds past {@code e}, given what it held once its operands were worked out.
     */
    private Walked pastOperands(Core e, Walked operands, Denotations at, InputReads reads) {
        // Every comparison this plan numbers is answered for, and answered under what holds once
        // its sides have answered: a run that stopped working a side out is no run arriving at it.
        if (e instanceof Core.Binary comparison) {
            outcomesAt(comparison, operands, at, reads);
        }
        answeredAt(e, operands.known());
        mayStopBefore(e, operands);
        if (operands.known().reachesNothing()) {
            // No run worked the operands out, so none makes this evaluation either.
            return operands;
        }
        // What a run past this evaluation holds is what its operands left with what its operator
        // asks of them, or nothing where it answers nothing. What is taken in there is a step on
        // the way like a condition, and a proof that leans on it names it.
        PathCompletion.Past past = completion.past(e, operands.known(), at, operands.mayStop());
        boolean narrowed = past.known() != operands.known();
        if (!narrowed && past.mayStop().equals(operands.mayStop())) {
            return operands;
        }
        List<PathDecision> answered = operands.decided();
        if (narrowed) {
            answered = new ArrayList<>(answered);
            answered.add(PathDecision.ofAnAnswer(e.pos()));
        }
        // Some run reaching here may not get past it, so what follows has something above it.
        return new Walked(past.known(), answered, past.mayStop(), false, false,
                WhyNone.BY_THE_WAY, false);
    }

    /**
     * What a run leaving a condition holds, and what it holds having got {@code true} out of it
     * and having got {@code false}.
     *
     * <p>Each is what the runs that worked the condition out and got that value hold: where a
     * short circuit's right answers nothing, no run gets {@code true} out of {@code &&} and the
     * state for it is empty, while the {@code false} left by the left side is not.
     */
    private record Exits(Walked completed, Walked whenTrue, Walked whenFalse) {

        /** A condition read as one step: both values are got from where it left. */
        static Exits of(Walked completed) {
            return new Exits(completed, completed, completed);
        }

        Walked when(boolean value) {
            return value ? whenTrue : whenFalse;
        }
    }

    /**
     * {@code e} worked out, with what each value it gets leaves. Only a short circuit has exits of
     * its own; any other condition leaves what it left whichever value it got.
     */
    private Exits exitsOf(Core e, Walked here, Denotations at, InputReads reads) {
        if (here.known().reachesNothing()) {
            return Exits.of(walk(e, here, at, reads));
        }
        // A value standing as a wider type is the value it holds, with what the widening itself
        // makes of it on top; the exits are the held value's.
        Exits operands = switch (e) {
            case Core.Widen widen -> exitsOf(widen.value(), here, at,
                    reads.entering(ScopeStep.SAME, symbols, newtypes));
            case Core.Binary binary when binary.op().stopsWhenItsAnswerIsSettled() ->
                    shortCircuitOperands(binary, here, at, reads);
            default -> null;
        };
        if (operands == null) {
            return Exits.of(walk(e, here, at, reads));
        }
        Walked past = pastOperands(e, operands.completed(), at, reads);
        return past == operands.completed() ? operands : Exits.of(past);
    }

    /**
     * The operands of a short circuit worked out, with the exits their order gives it.
     *
     * <p>The value the operator reaches its right side for is got only by a run that worked the
     * right out and got it there; the other value is got by a run the left settled or by one that
     * worked the right out and got it. A run that did not get past the right gets neither.
     */
    private Exits shortCircuitOperands(Core.Binary binary, Walked here, Denotations at,
                                       InputReads reads) {
        Exits left = exitsOf(binary.left(), here, at, reads);
        if (left.completed().known().reachesNothing()) {
            // No run gets past the left, so the right is a place nothing arrives at.
            walk(binary.right(), left.completed(), at, reads);
            return Exits.of(left.completed());
        }
        // Which way the left has to come out for the right to run is the operator's own
        // answer, and the same answer says there is a right side that runs only sometimes.
        // Read the other way round, a comparison guarded by its neighbour would be read
        // against conditions nothing on the way to it established.
        boolean reachedWhen = binary.op().rightRunsWhenLeftIs();
        Walked before = left.when(reachedWhen);
        Predicates.Assumed reaching = assuming(binary.occurrence(),
                MeaningsOfABody.Part.Asked.LEFT, binary.left(), before.known(), at, reads,
                reachedWhen);
        Exits right = exitsOf(binary.right(), before.at(reaching.known(),
                with(before.decided(), reaching, binary.left().pos(), reachedWhen)), at, reads);
        // A run leaves the operator having run the right, or with the left settling it.
        // Which the left settling holds is asked only where no run leaves having run the
        // right: otherwise a run leaving holds what held after the left either way, and
        // the left is what stands for that way.
        // The left's own exit for that value and not what it left whichever value it got: where
        // the left gets the value from no run, nothing settles it here either.
        Walked settled = left.when(!reachedWhen);
        if (right.completed().known().reachesNothing()) {
            Predicates.Assumed settling = assuming(binary.occurrence(),
                    MeaningsOfABody.Part.Asked.LEFT, binary.left(), settled.known(), at,
                    reads, !reachedWhen);
            settled = settled.at(settling.known(),
                    with(settled.decided(), settling, binary.left().pos(), !reachedWhen));
        }
        Walked completed = leaving(left.completed(), List.of(right.completed(), settled));
        Walked other = alternatives(left.completed(), List.of(settled, right.when(!reachedWhen)));
        return reachedWhen
                ? new Exits(completed, right.whenTrue(), other)
                : new Exits(completed, other, right.whenFalse());
    }

    /**
     * What a run holds that left by any of {@code ways}: the one way where a single way leaves
     * anything, since there is nothing to join it with.
     */
    private static Walked alternatives(Walked fork, List<Walked> ways) {
        Walked joined = leaving(fork, ways);
        List<Walked> left = ways.stream().filter(way -> !way.known().reachesNothing()).toList();
        return left.size() == 1 ? joined.at(left.get(0).known(), left.get(0).decided()) : joined;
    }

    /**
     * What a walk leaves once it has worked a node out.
     *
     * @param known        what a run past it holds
     * @param decided      the steps on the way to it that were taken in
     * @param mayStop      what on the way may stop a run for what nothing here says
     * @param nothingAbove whether nothing on the way decided anything or may have stopped a run —
     *                     which a part of a fork read with nothing above it reads a witness off
     * @param noneStopped  whether every run that got to where this walk began got past all it
     *                     worked out, as far as anything shows: false where something it worked out
     *                     answered on some runs only, said or not. What a fork's ways leave is
     *                     read off it ({@link #leaving}), since each way begins with a fork above it
     *                     and so with {@code nothingAbove} false
     * @param whyNoneLeft  why no run gets here, where none does ({@link #whyNothingArrives})
     * @param filedAbove   where no run gets here, whether an arm on the way was filed as one
     *                     nothing enters — which is then the finding, and no arm below is filed
     *                     again. False where what left nothing was something worked out, which
     *                     files no arm, so the first fork past it is filed ({@link #noneEnters})
     */
    private record Walked(Known known, List<PathDecision> decided, List<WhatMayStopARun> mayStop,
                          boolean nothingAbove, boolean noneStopped, WhyNone whyNoneLeft,
                          boolean filedAbove) {

        /** Where a body's walk begins: nothing decided and nothing worked out yet. */
        static Walked entering(Known known) {
            return new Walked(known, List.of(), List.of(), true, true, WhyNone.BY_THE_WAY, false);
        }

        /** The same way on, under {@code known} and with the steps {@code decided}. */
        Walked at(Known known, List<PathDecision> decided) {
            return new Walked(known, decided, mayStop, nothingAbove, noneStopped, whyNoneLeft,
                    filedAbove);
        }

        /**
         * One way out of a fork decided here, under {@code known} and with {@code decided} —
         * where {@code known} leaves nothing, the fork has filed the arm the way is.
         */
        Walked enteringAWay(Known known, List<PathDecision> decided) {
            return new Walked(known, decided, mayStop, false, true, WhyNone.BY_THE_WAY,
                    known.reachesNothing());
        }

        /** This, below an arm filed as one nothing enters. */
        Walked filed() {
            return new Walked(known, decided, mayStop, nothingAbove, noneStopped, whyNoneLeft,
                    true);
        }

        /**
         * This, past a call that applies a closure whose body walked to {@code body}: where
         * anything in it answered on some runs only, the call may stop a run, and nothing here
         * holds which.
         */
        Walked pastAnApplicationOf(Walked body) {
            if (body.noneStopped()) {
                return this;
            }
            Set<WhatMayStopARun> stops = new LinkedHashSet<>(mayStop);
            stops.add(new WhatMayStopARun.ACall());
            return new Walked(known, decided, List.copyOf(stops), false, false, whyNoneLeft,
                    filedAbove);
        }

        /**
         * Why no run gets here, where none does and something here says why. Empty where nothing
         * does — no step taken in on the way names what left nothing — and then nothing is filed
         * on it.
         */
        Optional<Proof> whyNothingArrives() {
            return switch (whyNoneLeft) {
                case WhyNone.Because(Proof proof) -> Optional.of(proof);
                case WhyNone.Unsaid _ -> Optional.empty();
                case WhyNone.ByTheWay _ -> decided.isEmpty() ? Optional.empty()
                        : Optional.of(Proof.conditionsThatCannotAllHold(decided));
            };
        }
    }

    /** Why no run gets to where a walk stands, as far as anything here says it. */
    private sealed interface WhyNone {

        /** The steps taken in on the way, where they name anything. */
        WhyNone BY_THE_WAY = new ByTheWay();

        /** The steps taken in on the way. */
        record ByTheWay() implements WhyNone {}

        /** This, and not the steps on the way: every way out of a fork left nothing for its own
         *  reason, or the closure the walk is in is applied to nothing. */
        record Because(Proof proof) implements WhyNone {}

        /** Every way out of a fork left nothing, and not every way says why. */
        record Unsaid() implements WhyNone {}
    }

    /**
     * What a run leaving a fork holds, from {@code fork} where it was decided and what each of
     * {@code ways} out of it left.
     *
     * <p>Nothing where no way out leaves anything, and then why is every way's reason together.
     * Otherwise what held at the fork: a way is read in an environment of its own and two ways have
     * no join here, so what held at the fork is what they agree on. What may stop a run is what
     * may stop one on a way some run leaves by, since a way nothing leaves is no way a run past the
     * fork came. Something is above what follows where any way stopped a run — one nothing leaves
     * among them, where something it worked out answered nothing — and a way the fork shut is not
     * one: no run stopped there, they went the other way.
     */
    private static Walked leaving(Walked fork, List<Walked> ways) {
        List<Walked> left = ways.stream().filter(way -> !way.known().reachesNothing()).toList();
        if (left.isEmpty()) {
            List<Proof> each = new ArrayList<>();
            for (Walked way : ways) {
                way.whyNothingArrives().ifPresent(each::add);
            }
            WhyNone why = each.size() == ways.size()
                    ? new WhyNone.Because(Proof.everyAlternativeRuledOut(each))
                    : new WhyNone.Unsaid();
            return new Walked(fork.known().reachingNothing(), fork.decided(), fork.mayStop(),
                    false, false, why, false);
        }
        Set<WhatMayStopARun> stops = new LinkedHashSet<>(fork.mayStop());
        left.forEach(way -> stops.addAll(way.mayStop()));
        boolean through = ways.stream().allMatch(Walked::noneStopped);
        return new Walked(fork.known(), fork.decided(), List.copyOf(stops),
                fork.nothingAbove() && through, fork.noneStopped() && through,
                WhyNone.BY_THE_WAY, false);
    }

    /**
     * That a run arriving at {@code e} — a comparison a line is drawn at, or an application whose
     * answer states one — may have stopped on the way for what nothing here says, where it may.
     *
     * <p>Filed beside what arrives and not inside it. What arrives is what has to hold for a run to
     * be there; this is whether that is all there is to getting there, which a reader asking whether
     * a row at the line is one some run makes needs, and one dropping a line does not.
     */
    private void mayStopBefore(Core e, Walked operands) {
        if (operands.mayStop().isEmpty() || operands.known().reachesNothing()) {
            return;
        }
        ConstructOccurrence comparison = e instanceof Core.Binary binary
                ? numbered(binary, plan) : null;
        if (comparison != null) {
            stopsBefore.put(comparison, operands.mayStop());
        }
        plan.applicationAnsweringAt(e).ifPresent(application ->
                stopsBefore.put(application, operands.mayStop()));
    }

    /** Every arm of a fork in {@code arms} the walk has not proven otherwise, as one nothing enters
     *  for {@code why}. */
    private void noneEnters(ControlPlace.Arm[] arms, Proof why) {
        if (arms == null) {
            return;
        }
        for (ControlPlace.Arm arm : arms) {
            if (!(out.get(arm) instanceof Reachability.Unreachable)) {
                out.put(arm, new Reachability.Unreachable(why));
            }
        }
    }

    /** Every arm in {@code e}, as one nothing arrives at for {@code why}. */
    private void appliedToNothing(Core e, Proof why) {
        ControlPlace.Arm[] arms = plan.armsOf(e);
        if (arms != null) {
            for (ControlPlace.Arm arm : arms) {
                out.put(arm, new Reachability.Unreachable(why));
            }
        }
        Core.forEachChild(e, child -> appliedToNothing(child, why));
    }

    /**
     * Every comparison below a place nothing arrives at, answered as one nothing arrives at.
     *
     * <p>A separate descent because what it does is not what the walk does: no arm is filed, and
     * nothing here narrows anything — the state was already empty when this began, and it stays
     * that way for every node under it. Whether one operand of a short circuit was reached is a
     * question about a run, and there are none.
     *
     * <p>Written out rather than folded into the walk, because the walk stops here and stopping is
     * what it is for. Read as one thing, the walk answered for whatever it happened to reach:
     * {@code A && (B || C)} with {@code A} ruled out stops at the operator, which is numbered
     * nowhere, and left {@code B} and {@code C} unanswered — the shape of a claim nothing made.
     */
    private void unreached(Core e, Walked here, Denotations at, InputReads reads) {
        if (e instanceof Core.Binary comparison) {
            outcomesAt(comparison, here, at, reads);
        }
        answeredAt(e, here.known());
        Walked below = here;
        ControlPlace.Arm[] arms = plan.armsOf(e);
        Optional<Proof> why = here.whyNothingArrives();
        if (arms != null && !here.filedAbove() && why.isPresent()) {
            noneEnters(arms, why.get());
            below = here.filed();
        }
        Walked under = below;
        Core.forEachChild(e, child -> unreached(child, under, at, reads));
    }

    /**
     * What arrives at {@code node}, where an application the model states answers there.
     *
     * <p>A line is drawn on what such an application means — an emptiness check states a size
     * against nought — and is dropped by the same fact a comparison's is: nothing arriving where it
     * is asked. So what arrives is filed under the application, the way it is under a comparison.
     *
     * <p>Whether anything arrives, and no projection beside it. A projection says where the value at
     * one position lies, read off the side of a comparison that is that position; an application
     * has arguments and no side, and what it states is about a number of what stands there rather
     * than the value itself — which is not what a reader applying a projection asks of it.
     */
    private void answeredAt(Core node, Known k) {
        plan.applicationAnsweringAt(node).ifPresent(application -> arriving.put(application,
                k.reachesNothing()
                        ? new ComparisonArrival.NothingArrives()
                        : new ComparisonArrival.NoProjection()));
    }

    /**
     * One comparison, answered both ways, under what holds where it stands.
     *
     * <p>Which nodes get an answer is the plan's to say and not this walk's. Read off the shape of
     * a fork's condition, the reading answered for the comparisons a fork was written directly
     * around and silently for no others — and a comparison nothing answered for reads, everywhere
     * below, exactly like one answered "nothing is known".
     *
     * <p>Empty is an ordinary answer here: the node is not a comparison, or is one this plan
     * numbered nothing at, and either way there is no place a run through it would be recorded.
     */
    private void outcomesAt(Core.Binary comparison, Walked here, Denotations at,
                            InputReads reads) {
        // What arrives is about the comparison and not about either way out of it, so it is filed
        // under the comparison the plan names and asked of the plan directly.
        ConstructOccurrence which = numbered(comparison, plan);
        if (which == null) {
            return;
        }
        Known k = here.known();
        arriving.put(which, arrivalAt(comparison, k, at, reads));
        for (boolean result : new boolean[] {true, false}) {
            Optional<ControlPlace.Outcome> where =
                    plan.outcomeOf(which, result);
            if (where.isEmpty()) {
                continue;
            }
            Optional<Proof> none = k.reachesNothing() ? here.whyNothingArrives() : Optional.empty();
            if (none.isPresent()) {
                // Neither way is one a run comes out of, for the reason nothing arrives.
                out.put(where.get(), new Reachability.Unreachable(none.get()));
                continue;
            }
            Predicates.Assumed taken = assuming(comparison.occurrence(),
                    MeaningsOfABody.Part.Asked.ITSELF, comparison, k, at, reads, result);
            out.put(where.get(), taken.known().reachesNothing()
                    ? new Reachability.Unreachable(Proof.conditionsThatCannotAllHold(
                            with(here.decided(), taken, comparison.pos(), result)))
                    : new Reachability.Unsettled(whyNot(taken, comparison)));
        }
    }

    /**
     * What arrives at {@code comparison}, from the state before the comparison is taken either way.
     *
     * <p>The one place a {@link souther.compiler.reach.ComparisonArrival} is made, so the order of
     * the questions is fixed here and nowhere has to remember it. The whole state answers first:
     * bounds read off an empty state say nothing — the predicates alone can empty it and leave every
     * numeric reading untouched — so a {@code Values} built without asking would publish a wide-open
     * projection of an arrival that is a contradiction.
     *
     * <p>The position and the interval come off the same side of the comparison. What the fact
     * means is "the value at this path, among what arrives, lies here", and a reader applies it only
     * where its own quantity is that path's value — so a comparison this cannot say that of answers
     * {@code NoProjection}, which restricts nothing.
     */
    private souther.compiler.reach.ComparisonArrival arrivalAt(Core.Binary comparison, Known k,
                                                               Denotations at, InputReads reads) {
        if (k.reachesNothing()) {
            return new souther.compiler.reach.ComparisonArrival.NothingArrives();
        }
        Core side = comparedSideIn(comparison, reads);
        TermPath position = side == null ? null : pathUnder(side, reads);
        FactSubject atom = side == null ? null : engine.terms().atomOf(side, at);
        if (position == null || atom == null) {
            return new souther.compiler.reach.ComparisonArrival.NoProjection();
        }
        return new souther.compiler.reach.ComparisonArrival.Values(position,
                k.numbers().boundsOf(atom));
    }

    /**
     * How it was shown that nothing arrives at an arm.
     *
     * <p>Two things can contradict a branch and they send an author to different places. What the
     * declarations guarantee of an input holds wherever the branch stands, so a condition that
     * leaves nothing against the entry facts alone is ruled out by the position and not by anything
     * on the way; everything else is the conditions on the way, taken together.
     *
     * <p>Asked by putting the condition to the entry facts again rather than by reading which
     * domain went empty: what is wanted is whether the guards above did any of the work, and that
     * is a question about those two states and not about how either was reached.
     */
    private Proof why(Core.If iff, boolean holds,
                      List<PathDecision> under, InputReads reads) {
        Core cond = iff.cond();
        if (assuming(iff.place().occurrence(), MeaningsOfABody.Part.Asked.CONDITION, cond, entry,
                entered, reads, holds).known().reachesNothing()) {
            TermPath position = comparedPositionIn(cond, reads);
            NumericDomain.Bounds admits = position == null ? null : valueBoundsAt(position);
            ValuesNamed named = position == null || read.at(position) == null ? null
                    : ValuesNamed.of(read.at(position).admitted().approximation());
            if ((admits != null || named != null) && !under.isEmpty()) {
                return Proof.outsideInputDomain(position, admits, named,
                        under.get(under.size() - 1));
            }
        }
        return Proof.conditionsThatCannotAllHold(under);
    }

    /** The position a comparison turns on, where it turns on exactly one this reading knows. */
    private TermPath comparedPositionIn(Core cond, InputReads reads) {
        Core side = comparedSideIn(cond, reads);
        return side == null ? null : pathUnder(side, reads);
    }

    /** The side of a comparison that is that one position, where there is exactly one. One
     *  decision for the proof above and the arrival, so the two cannot name different sides. */
    private Core comparedSideIn(Core cond, InputReads reads) {
        if (!(Core.withoutStanding(cond) instanceof Core.Binary b)) {
            return null;
        }
        TermPath left = pathUnder(b.left(), reads);
        TermPath right = pathUnder(b.right(), reads);
        return left != null && right == null ? b.left()
                : right != null && left == null ? b.right() : null;
    }

    /** Where a side of a comparison sits, reading through a newtype's own value. */
    private TermPath pathUnder(Core side, InputReads reads) {
        TermPath here = positionOf(side, reads);
        return here != null ? here
                : Core.withoutStanding(side) instanceof Core.FieldAccess field
                        ? positionOf(field.target(), reads)
                : Core.withoutStanding(side) instanceof Core.FieldProjection projection
                        ? positionOf(projection.target(), reads) : null;
    }

    /** Where {@code e} stands, and null where it stands nowhere or was not read — which are one
     *  answer to a reader asking whether the guards above reach a position. */
    private TermPath positionOf(Core e, InputReads reads) {
        return switch (reads.pathOf(e, newtypes)) {
            case PathResolution.At(var at) -> at;
            case PathResolution.NotAPosition _ -> null;
            // And one of several is not this position either. What the caller does with an answer
            // is prove a branch unreachable by what the rules leave at the position — a proof about
            // one place — so a name that stands at one of two places on two runs is one no such
            // proof can be made about, whichever of them it turns out to be.
            case PathResolution.MayStandAt _, PathResolution.MadeOf _ -> null;
        };
    }

    /**
     * What the rules leave the value standing at {@code position}, where they leave it a range at
     * all.
     *
     * <p>That number and never another of the place. What the caller has is a comparison one side of
     * which is this position, and what it goes on to say is that the branch asks for values the
     * position cannot hold — so the range wanted is the range of what stands there. A count taken of
     * the position is a number of its own with a range of its own, and offered here it would prove a
     * branch unreachable by where a length falls.
     *
     * <p>No falling back to whatever range the position happens to have. A position with no answer
     * about the values standing at it is one this says nothing about, which is what the caller does
     * where it is handed null.
     */
    private NumericDomain.Bounds valueBoundsAt(TermPath position) {
        Position at = read.at(position);
        PositionBounds bounds = at == null ? null : at.boundsFor(new NumericTerm.ValueOf(position));
        NumericDomain.Bounds admits = bounds == null ? null : bounds.admissible();
        return admits == null || admits.saysNothing() ? null : admits;
    }

    /**
     * Why an arm this could not prove is left as it was.
     *
     * <p>Two ways of settling nothing, and they are owed different things. A condition of a shape
     * no rule here reads is this compiler's limit, and widening the reading removes it; a condition
     * read to no effect is the ordinary state of a branch nobody built a value for, and no widening
     * touches it. Told apart by asking the reading, not by comparing the state it answered with to
     * the state it was given — that comparison says whether anything changed, which is neither.
     *
     * <p>The shape and not what was taken in. Since every value has an identity, a condition this
     * could not read still narrows the state through the subject it names — so "something was taken
     * in" stopped telling the two apart, and what an author is owed here is whether the reading
     * reached what the condition says.
     */
    private static WhyUnsettled whyNot(Predicates.Assumed taken, Core cond) {
        return taken.shapeRead() ? WhyUnsettled.noWitness()
                : WhyUnsettled.aConditionWasNotRead(cond.pos(), taken.notTaken());
    }

    /**
     * The conditions on the way here, with this one — where it was taken in at all.
     *
     * <p>The only way one of these is made, so that a proof cannot name a condition the domains
     * never took in. A condition nothing was taken from narrowed nothing: what came out is what went
     * in, and listing it among the reasons would say a line was holding when nothing here could tell
     * whether it was.
     *
     * <p>What was taken in, and not what was read. A condition whose shape ran out still narrows the
     * state through the subject it names, and it may be the whole of why nothing stands here — left
     * out, this proof would name the conditions that <em>were</em> read and say they cannot all hold
     * when they plainly can, which is a claim about the model made out of a limit of this compiler.
     */
    private static List<PathDecision> with(List<PathDecision> decided, Predicates.Assumed taken,
                                           SourcePos at, boolean held) {
        if (!taken.taken()) {
            return decided;
        }
        List<PathDecision> out = new ArrayList<>(decided);
        out.add(PathDecision.ofACondition(at, held));
        return out;
    }

    /**
     * The forks on the way here, with {@code arm} taken — where taking it {@code settled}
     * something of the value it matched, which is the same rule as for a condition: an arm nothing
     * was taken from narrowed nothing.
     */
    private static List<PathDecision> taking(List<PathDecision> decided, Core.Case arm,
                                             boolean settled) {
        if (!settled) {
            return decided;
        }
        List<PathDecision> out = new ArrayList<>(decided);
        out.add(new PathDecision(arm.pos(), PathDecision.Way.TAKEN));
        return out;
    }

    /**
     * One arm of a fork, read under its own side of the condition.
     *
     * <p>The answer is filed at the arm and the walk goes on inside it. Where the condition leaves
     * nothing, the arm is proven and what is under it is not walked: everything there is unreachable
     * for the same reason, and one finding is what an author is owed.
     *
     * <p>Where {@code noRunPast} says no run got past working the condition out, {@code fork} is
     * where the condition began, and the arm is still held to what the condition states there,
     * which is what proves an arm the rules shut. Any other arm is proven by {@code noRunPast},
     * and what is inside it is walked as a place nothing arrives at.
     *
     * @param fork what holds where the arm is decided: once the condition is worked out, or before
     *             it where {@code noRunPast} is given
     * @return what a run leaving the arm holds
     */
    private Walked enterArm(ControlPlace.Arm[] arms, int index, Core.If iff, Core arm,
                           Walked fork, Optional<Proof> noRunPast, Denotations at,
                           InputReads reads, boolean holds) {
        Predicates.Assumed taken = assuming(iff.place().occurrence(),
                MeaningsOfABody.Part.Asked.CONDITION, iff.cond(), fork.known(), at, reads, holds);
        Known inside = taken.known();
        List<PathDecision> under = with(fork.decided(), taken, iff.cond().pos(), holds);
        if (arms != null && index < arms.length) {
            out.put(arms[index], inside.reachesNothing()
                    ? new Reachability.Unreachable(why(iff, holds, under, reads))
                    : noRunPast.<Reachability>map(Reachability.Unreachable::new)
                            .orElseGet(() -> new Reachability.Unsettled(
                                    whyNot(taken, iff.cond()))));
        }
        return walk(arm, fork.enteringAWay(
                        noRunPast.isPresent() ? inside.reachingNothing() : inside, under), at,
                reads.choosing(Choice.Decides.ofCondition(iff, holds), symbols, newtypes));
    }

    /**
     * Every arm of a {@code match}, held against what the rules leave the position matched on.
     *
     * <p>A different question from a condition's, and answered from a different place. A condition
     * narrows the path to an arm; a case is one the rules of the position refuse or leave, which is
     * as true three arms deep as at the first fork — a refusal is unconditional.
     *
     * <p>The other direction is not. That the rules <em>leave</em> a case says a caller can supply
     * one, which says something about arriving here only where nothing stands above: a fork the
     * body reaches first is reached by the behavior being applied at all. So the witness takes both
     * — every rule of the position read and leaving the case, and nothing decided on the way — and
     * is built here where both are in hand rather than assembled by whoever asks.
     *
     * <p>And an arm the rules leave may still be one the way here does not: a fork further out on
     * the same value took other cases of it, or a condition settled whether it holds anything. That
     * is the forks on the way, this arm among them, and is asked of what holds here.
     */
    private void cases(Core.Match match, Known k, Denotations in, InputReads reads,
                       List<PathDecision> decided, boolean nothingAbove) {
        ControlPlace.Arm[] arms = plan.armsOf(match);
        if (arms == null) {
            return;
        }
        // Whether any value arrives at an arm is decided in one place, which every reader of an arm
        // asks, wherever the scrutinee stands: a position of the input, a value the source wrote,
        // or a value the body works out whose cases are read off the input. What this adds is the
        // witness, which only a scrutinee at a position of the input can have.
        WhatTheDeclarationsLeaveAnArm ruling = WhatTheDeclarationsLeaveAnArm.of(match, reads,
                symbols, newtypes, meanings, reading);
        TermPath path = positionOf(match.scrutinee(), reads);
        // The reading this walk was given, which is the one held here. Which location the name
        // stands for is the environment's answer and what the rules leave there is the reading's,
        // and neither is asked of the other.
        Position at = path == null ? null : read.at(path);
        for (int i = 0; i < match.cases().size() && i < arms.length; i++) {
            Core.Case arm = match.cases().get(i);
            Optional<Proof> proof = ruling.ruledOut(i).flatMap(why -> proofOf(why, arm));
            if (proof.isPresent()) {
                out.put(arms[i], new Reachability.Unreachable(proof.get()));
                continue;
            }
            if (engine.takingItsCases(arm, match.scrutinee(), k, in).reachesNothing()) {
                out.put(arms[i], new Reachability.Unreachable(Proof.conditionsThatCannotAllHold(
                        taking(decided, arm, true))));
                continue;
            }
            if (path == null) {
                continue;
            }
            // A position this reading never got to — deeper than it reads into what a parameter
            // holds — states no such distinction, which is the position's own answer and not this
            // walk's. Said in its words so that a claim below the depth is told what it is told
            // everywhere else.
            Reachability said = at == null
                    ? new Reachability.Unsettled(WhyUnsettled.thePositionDidNotSettleIt(
                            new Unsettlement.NoSuchDistinction()))
                    : witnessOf(at, path, arm, nothingAbove);
            if (said != null) {
                out.put(arms[i], said);
            }
        }
    }

    /**
     * {@code why} as a proof an author reads, or empty where it has no words.
     *
     * <p>What rules a way out is what the declaration or the rules leave the value matched on, and
     * a composite is ruled out where every way in it is: those are the proofs said here. The
     * numbers a comparison is over, a container that holds nothing, and a statement that never
     * holds are what a {@code match} arm does not state — an arm selects by the cases of a value —
     * so there is no sentence for them, and an arm ruled out by one would be left as one nothing
     * was shown about rather than given a sentence written for something else.
     */
    private static Optional<Proof> proofOf(WhyNoValueTakesTheArm why, Core.Case arm) {
        return switch (why) {
            case WhyNoValueTakesTheArm.ByWhatIsWritten(var canBe, var cases) ->
                    Optional.of(Proof.noCaseTheValueCanBeIsTaken(canBe, cases));
            case WhyNoValueTakesTheArm.ByTheRulesOfThePosition(var at, var cases) ->
                    Optional.of(Proof.everyCaseRefused(at.toString(), cases));
            case WhyNoValueTakesTheArm.ByWhatItStates(var stated) -> proofOf(stated, arm);
        };
    }

    private static Optional<Proof> proofOf(WhyRuledOut why, Core.Case arm) {
        return switch (why) {
            case WhyRuledOut.TheDeclarationLeavesNone(var at, var declared, var asked,
                                                      var among) ->
                    Optional.of(Proof.theDeclarationLeavesNoCase(at.toString(), declared, asked,
                            among));
            case WhyRuledOut.TheRulesRefuseEveryCase(var at, var refused) -> {
                List<TypeSymbol> leaves = new ArrayList<>();
                for (Case each : refused) {
                    if (!(each instanceof Case.SumCase sum)) {
                        yield arm.caseTypes().isEmpty() ? Optional.empty()
                                : Optional.of(Proof.everyCaseRefused(at.toString(),
                                        arm.caseTypes()));
                    }
                    leaves.add(sum.leaf());
                }
                yield Optional.of(Proof.everyCaseRefused(at.toString(), leaves));
            }
            case WhyRuledOut.EveryWay(var each) -> {
                List<Proof> proofs = new ArrayList<>();
                for (WhyRuledOut one : each) {
                    Optional<Proof> proof = proofOf(one, arm);
                    if (proof.isEmpty()) {
                        yield Optional.empty();
                    }
                    proofs.add(proof.get());
                }
                yield Optional.of(Proof.everyAlternativeRuledOut(proofs));
            }
            case WhyRuledOut.ItNeverComesOutSo _, WhyRuledOut.TheNumbersLeaveNone _,
                 WhyRuledOut.NothingIsHeldIn _ -> Optional.empty();
        };
    }

    /** The distinctions {@code arm} reaches, read off the checker's resolution of it. */
    private static List<Refinement> reachedBy(Core.Case arm) {
        List<Refinement> reaches = new ArrayList<>();
        for (ResolvedCase each : arm.pattern().cases()) {
            reaches.addAll(Refinement.allOf(each));
        }
        return reaches;
    }

    /**
     * That a value arrives at an arm nothing ruled out, where that is shown, or null where the arm
     * names no case — a binding of the whole value, which the rules of the position say nothing
     * about.
     *
     * <p>Not ruled out is no witness. What is one is every case the arm is written for left
     * standing by the rules of the position, so a caller can supply one, and nothing standing above
     * the fork, so that supplying one arrives here: a fork the body reaches first is reached by the
     * behavior being applied at all.
     *
     * <p><b>Asked of the distinctions the arm reaches and not of the names it is written by.</b> A
     * name is not a distinction of a position: an optional's carriers name none of them, and a case
     * that is itself a sum names the leaves under it rather than any one of them. What the arm
     * reaches is the checker's resolution of it, read as distinctions where the two vocabularies
     * agree.
     */
    private Reachability witnessOf(Position at, TermPath path, Core.Case arm,
                                   boolean nothingAbove) {
        if (arm.caseTypes().isEmpty()) {
            return null;
        }
        boolean oneLeft = false;
        for (Refinement each : reachedBy(arm)) {
            switch (at.admissionOf(each)) {
                case Admits.Unsettled unsettled -> {
                    return new Reachability.Unsettled(
                            WhyUnsettled.thePositionDidNotSettleIt(unsettled.why()));
                }
                case Admits.Admitted _ -> oneLeft = true;
                case Admits.Refused _ -> { }
            }
        }
        // Some case the arm is written for is one the rules leave, and the ones they refuse are not
        // what a caller supplies. None left is no witness: that is a proof of the other kind, and it
        // is made above where it is made at all.
        if (!oneLeft) {
            return new Reachability.Unsettled(WhyUnsettled.noWitness());
        }
        return nothingAbove
                ? new Reachability.Reachable(
                        Witness.everyRuleReadAndNothingAbove(path.toString()))
                : new Reachability.Unsettled(WhyUnsettled.noWitness());
    }
}
