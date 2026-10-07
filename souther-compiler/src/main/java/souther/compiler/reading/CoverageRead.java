package souther.compiler.reading;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.check.Choice;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.NormalReturn;
import souther.compiler.coverage.RunBodies;
import souther.compiler.coverage.UnreachableReasons;
import souther.compiler.flow.ValueArrivals;
import souther.compiler.flow.Ways;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * One reading of a body's decisions: where a run can get to, and what holds on the way.
 *
 * <p>What a black-box measure has to assume about every pair of inputs, read instead. Every measure
 * over a body reads control flow — which arms were entered — and passing through all four arms of
 * {@code if A { if B { X } else { Y } } else { Z }} says nothing about whether the interactions
 * between A and B were tried. This reads what a value owes itself to, and what it takes to arrive
 * anywhere in the body.
 *
 * <p>One walk and several facts, which is why the walk is here rather than inside any of them. What
 * holds on the way to a place is one thing about the body, and the readings that want it want it for
 * different work: {@link Meetings} asks it of the places where decisions determine one value
 * together, {@link Arms} of every arm the plan numbered. A reading given its own walk would be a
 * second reading of the same body, free to disagree with this one the day either of them moves —
 * which is how a fact came to be spelled twice before. So what is shared here is where the walk goes
 * and what holds there; what is found is each collector's own, and so is the state finding it needs.
 *
 * <p>What stops is the reading and never the classification. A place no run reaches, and one this
 * reading has no words for, are both places whose arms the plan numbered and a measure will ask
 * about — so the walk goes on through them carrying what it came to, and every arm inside is told
 * which of those it is. Stopping the walk instead left those arms out of the answer, and an arm left
 * out is an arm somebody has to decide the meaning of.
 *
 * <p>Which position a decision is about is {@link InputReads}'s answer and not this one's. A name is
 * not a position — a helper spliced into a body binds the call's argument to the helper's own
 * parameter and matches that, so a reading that took the word would say about one parameter what is
 * true of another. Two environments are carried down for that reason and they answer different
 * questions: {@code InputReads} says which position a name points at, and the bindings here say
 * what the value at a name was settled by.
 *
 * <p>A path to a value and what the value is are two questions, and neither is asked here. Both are
 * {@link ValueArrivals}'s, read off the body once and asked of by whoever needs them — this walk and
 * the reading of whether an arm answers anything included. What is added here is the third question:
 * what to call a way, which is where the numbering comes in and is the only place it does. A
 * condition this can find no words for leaves a way {@link souther.compiler.flow.Completeness#PARTIAL}
 * and takes nothing away from what the body was read to do.
 *
 * <p>Under-reading is the safe direction. A group nothing formed is an obligation nobody is asked
 * for, which is where a product over the input positions already leaves things; a group formed too
 * eagerly asks for rows that establish nothing. Both limits below take that direction: a value that
 * can be settled more ways than the reading will tell apart is answered as settled one way, and a
 * position reached more ways than it will read at once is read the one way it used to be.
 */
public final class CoverageRead {

    /**
     * How many path contexts one position of the body will be read under.
     *
     * <p>A second amplification and not the one beside it. {@link CoverageNaming#MOST_OUTCOMES}
     * bounds the ways one value is read as being settled, which is a product taken at one node; this
     * bounds how many ways in one position is read under, which is a product taken along the way
     * down to it. A condition that fails four
     * ways standing inside another one is a meeting read sixteen times, so the two multiply with the
     * nesting of the body and neither bound holds what the other does.
     *
     * <p>The contexts that survive and not the alternatives the syntax offers. A way in settling a
     * decision that the way in above it settled the other way is no path at all, and letting it take
     * a share here would move where the bound falls with how the body is written rather than with
     * how much there is to read.
     *
     * <p>Counted and not estimated, which is why the walk carries the contexts of a position
     * together. How many of them survive is a fact about the position and about all the ways down to
     * it at once — a walk arriving one way at a time cannot know what the ways beside it came to,
     * and multiplying what it does know stands in for the answer without being it: uneven arms make
     * that product larger than the number of contexts there are, and a position under the bound is
     * given up on as though it were over.
     *
     * <p>Held by induction rather than by a running count. A position is read under at most this
     * many contexts, and what an arm below it is read under is either those held to the ways the
     * condition comes out — checked against the bound where it is built — or, over the bound, one
     * per context, which is what there already were.
     *
     * <p>Over the bound an arm is read the one way a fork whose condition this reading cannot value
     * is read, which is where every fork was before the ways in were told apart. Going over asks
     * for no more than was asked for then, and what an arm under it is told is that the limit is
     * what stopped this rather than anything about the body.
     */
    private static final int MOST_WAYS_IN = 16;

    /** The bodies a run of the behavior goes through, as the plan numbered them. */
    private final RunBodies run;

    /** What each body is read to arrive at, made of the body the walk is about to read. */
    private final Function<Core, ValueArrivals<Outcome>> readingOf;

    /**
     * What the body being walked was read to arrive at, and by which ways. Read once per body,
     * before the walk of it starts: what a node arrives at is a question about the body it is in.
     */
    private ValueArrivals<Outcome> reading;

    /** The body being walked, which the arms met in it are arms of. */
    private Core body;

    /** The cycle of calls the body being walked is on, as {@link RunBodies#cycleOf} names it;
     *  null while the behavior's own body is. */
    private Core cycle;

    /** The meetings this walk is read for, and the owner of everything finding a meeting takes. */
    private final Meetings meetings;

    /** How each arm the plan numbered is reached. */
    private final Arms arms;

    /** Every way a run of the body is known to take, in the order the walk met them. */
    private final Set<WayIn> taken = new LinkedHashSet<>();

    /** The parts a run arrives at and answers nothing from, in the order the walk met them. */
    private final List<NothingAnsweredHere> answersNothing = new ArrayList<>();

    /** Whether a node of the body being walked answers a value, made the first time it is asked. */
    private NormalReturn answering;

    /** How each cycle of calls is entered, joined over every call into it walked so far. */
    private final Map<Core, Entered> entered = new IdentityHashMap<>();

    /** The cycles of calls walked, after which nothing more may enter them. */
    private final Set<Core> read = Collections.newSetFromMap(new IdentityHashMap<>());

    private CoverageRead(RunBodies run, Function<Core, ValueArrivals<Outcome>> readingOf,
                         Meetings meetings, Arms arms) {
        this.run = run;
        this.readingOf = readingOf;
        this.meetings = meetings;
        this.arms = arms;
    }

    /**
     * How a run comes into a method: every way any call of it is reached, and whether a value
     * arrives at any of them.
     *
     * <p>One entry however many calls there are. A method is one body with one set of arms, so an
     * arm in it is reached wherever some call of the method is — read once per call, the last call
     * read would say alone how the arm is reached.
     */
    private record Entered(Reach reach, boolean observed) {

        Entered and(Entered other) {
            return new Entered(either(reach, other.reach), observed || other.observed);
        }
    }

    /**
     * What one walk over {@code body} came to.
     *
     * <p>Several facts and one reading. What each of them is about is its own accessor's business;
     * that they were read together is what this value says.
     *
     * @param interactions the groups, in the order the walk met them. A generation spending a row
     *                     budget over these takes them in this order, so which of them a budget that
     *                     runs out reaches is said by where the meeting is written and not by which
     *                     way round a fork above it a row goes
     * @param arms         one answer per arm of the behavior, by the number the plan gave it. Total
     *                     over the plan's arms: a key that is not there is not a thing to interpret,
     *                     because there is no such key.
     *
     *                     <p>In the order the plan holds them, which a caller composing a row at
     *                     each takes as the order to ask in — so what carries the order is the type
     *                     and not a habit of whatever map was handed over. Written as any map, an
     *                     unordered one was as admissible, and the order a plan is asked in would
     *                     have come from wherever that map put its keys
     * @param taken        every way some run of the body takes out of a fork, or settles a value
     *                     meeting another by, each as everything known to hold on it, in the order
     *                     the walk met them. What the body tells apart about its input, which is not
     *                     the ways in: a {@code match} past an attempted construction is reached by
     *                     a way in nothing states and is still a decision about the position it
     *                     matches on. Whole ways and never the decisions on them one at a time,
     *                     since a decision tells apart only what arrives where it is made — a
     *                     comparison under another one is made of the values the first let through
     * @param restOfTheBlock for each arm by which a run leaves a {@code guard} whose condition did
     *                       not hold, the arm the rest of the block is — which is where a run that
     *                       got past the guard went on — and the comparisons the guard decides by.
     *                       Both arms are arms of this read
     * @param answersNothing the parts of the bodies a run arrives at and answers no value from,
     *                       each the largest such part on its way down, in the order the walk met
     *                       them. Read on the same walk as the ways in, so the inputs said to reach
     *                       one are the inputs every other reading here says reach it
     */
    public record Read(List<Interaction> interactions,
                       java.util.SequencedMap<ArmProbe, PathAccess> arms,
                       List<WayIn> taken,
                       java.util.SequencedMap<ArmProbe, TheRestOfTheBlock> restOfTheBlock,
                       List<NothingAnsweredHere> answersNothing) {

        public Read {
            interactions = List.copyOf(interactions);
            taken = List.copyOf(taken);
            answersNothing = List.copyOf(answersNothing);
            arms = java.util.Collections.unmodifiableSequencedMap(
                    new java.util.LinkedHashMap<>(arms));
            restOfTheBlock = java.util.Collections.unmodifiableSequencedMap(
                    new java.util.LinkedHashMap<>(restOfTheBlock));
            for (java.util.Map.Entry<ArmProbe, TheRestOfTheBlock> each
                    : restOfTheBlock.entrySet()) {
                if (!arms.containsKey(each.getKey()) || !arms.containsKey(each.getValue().arm())) {
                    throw new IllegalArgumentException("a guard's two arms are arms of the read"
                            + " that says where its block goes on: " + each);
                }
            }
        }

        /** How arm {@code probe} is reached, by the number the plan gave it. */
        public PathAccess armAt(ArmProbe probe) {
            PathAccess access = arms.get(probe);
            if (access == null) {
                throw new IllegalArgumentException(
                        "arm " + probe + " is no arm of the behavior this read is of");
            }
            return access;
        }
    }

    /**
     * What the walk over the bodies a run of {@code behavior} goes through reads.
     *
     * <p>The bodies come with the plan of them, so what is read is where the plan numbered the
     * behavior's arms: its own body, and the methods of the values it calls. A method is read where
     * a call runs it, under what holds at the calls — a value takes no input, and whether a run
     * gets to its arms is whether it gets to a call of it.
     *
     * <p>Against the reading of the input the rest of the measurement reads, handed in rather than
     * made here. Made here, it is every rule of every parameter read again to the answers the
     * caller's reading already came to.
     */
    public static Read of(String behavior, RunBodies run, InputReading input) {
        CoverageSites.Plan plan = run.plan();
        RuleReadingSource source = input.rules();
        Symbols symbols = source.symbols();
        InputReads reads = InputReads.ofParameters(input.domain().parameterReads(),
                input.declared(), ElementBindings.NONE);
        // One reading of this body's comparisons, handed to both readers of them. What a way is
        // admitted by and what a decision is said of are two questions about one comparison, and
        // each reading it for itself is how they came to be about different numbers.
        souther.compiler.inputs.ComparedNumbers numbers =
                souther.compiler.inputs.ComparedNumbers.of(input);
        CoverageNaming naming =
                new CoverageNaming(plan, symbols, source.newtypes(), reads, numbers);
        Meetings meetings = new Meetings(plan);
        Arms arms = new Arms(plan);
        CoverageRead walked = new CoverageRead(run,
                body -> ValueArrivals.ofBody(body, naming,
                        new NumberWays(numbers, numbers.reading().quantities(), reads, symbols,
                                source.newtypes())),
                meetings, arms);
        walked.walkBody(run.entry(), null, naming,
                new Reach.Ways(List.of(new WayIn(List.of()))), true);
        // Each method after every body that calls into it, so it is entered every way it is
        // before it is read. One entering after its method was read is refused where it is made.
        for (Core method : run.methods()) {
            Core cycle = run.cycleOf(method);
            Entered into = walked.entered.get(cycle);
            if (into == null) {
                throw new IllegalStateException("the reading of `" + behavior + "` met no call of"
                        + " a method the run goes through; every call is one this walk goes to");
            }
            walked.walkBody(method, cycle, naming, into.reach(), into.observed());
        }
        List<Interaction> found = meetings.found();
        for (Interaction group : found) {
            walked.takesAt(group);
        }
        return new Read(found, arms.found(behavior), List.copyOf(walked.taken),
                arms.restOfTheBlock(behavior), walked.answersNothing);
    }

    /**
     * One body, read for what it arrives at and then walked under {@code reach}.
     *
     * @param onCycle the cycle of calls {@code root} is on, null for the behavior's own body
     */
    private void walkBody(Core root, Core onCycle, CoverageNaming naming, Reach reach,
                          boolean observed) {
        body = root;
        cycle = onCycle;
        reading = readingOf.apply(root);
        answering = null;
        if (onCycle != null) {
            read.add(onCycle);
        }
        walk(root, naming, reach, observed);
    }

    /**
     * That a run reaching a call of {@code method} under {@code reach} goes into it.
     *
     * <p>The way into the call is the way into the method, carried across rather than started
     * afresh: an arm in a value called only where some condition held is reached only there.
     *
     * <p>A call from a method to one on the same cycle of calls opens no way in. A run there came
     * into the cycle from outside it, by a call already joined into the way the cycle is entered.
     */
    private void enters(Core method, Reach reach, boolean observed) {
        Core into = run.cycleOf(method);
        if (into == cycle) {
            return;
        }
        if (read.contains(into)) {
            throw new IllegalStateException("a call of a method was met after the method was"
                    + " read; every caller of a method is read before it");
        }
        entered.merge(into, new Entered(reach, observed), Entered::and);
    }

    /**
     * That a run takes a way out of a fork, where {@code into} is how it comes to be on it.
     *
     * <p>As much as is known to hold there, which is the way the fork came out held to every way
     * the fork was reached by. A decision tells apart only what arrives where it is made, so it is
     * kept with what let a run get there; kept on its own it would split values that never reach
     * it. And a way no run takes is none: an arm for a case the way to the fork has already ruled
     * out tells apart cases that never arrive there.
     */
    private void takes(Reach into, Reach own) {
        if (!into.someRunArrives()) {
            return;
        }
        // Past the bound a way in is read no further, and nor is what is known on it: the fork's
        // own ways stand for it, which reads a decision against more than it was made in and
        // never against less.
        taken.addAll(into.known().size() > MOST_WAYS_IN ? own.known() : into.known());
    }

    /**
     * That a run reaching the meeting of {@code group} settles each value there each way the way in
     * to it leaves possible.
     *
     * <p>A comparison whose truth is handed on as a value is a decision no fork is taken by, and the
     * body tells its position apart all the same. Held to the way in to the meeting as a fork's ways
     * are held to the way in to the fork. A meeting is found only where a value arrives and its ways
     * in are named, so both are already settled here.
     */
    private void takesAt(Interaction group) {
        taken.add(new WayIn(group.reach()));
        for (Factor factor : group.factors()) {
            for (Outcome outcome : factor.outcomes()) {
                List<Decision> both = CoverageNaming.merge(group.reach(), outcome.holds());
                if (both != null) {
                    taken.add(new WayIn(both));
                }
            }
        }
    }

    /**
     * @param reach    every way in this position is reached by, together rather than one at a time,
     *                 because how many there are is what {@link #MOST_WAYS_IN} bounds and no one of
     *                 them can say — or what this reading has instead of them
     * @param observed whether a value arrives here at all. A subtree that arrives at none is one no
     *                 row observes: the decisions inside an arm that aborts are made and then thrown
     *                 away with the run, so a group found in there would be offered rows that settle
     *                 nothing. What it takes to get in there is unaffected — a run does arrive — so
     *                 the arms inside are read as they are anywhere else
     */
    private void walk(Core node, CoverageNaming naming, Reach reach, boolean observed) {
        if (node == null) {
            // The hole a refused clause leaves. What is missing is missing, and the arm it was the
            // body of is still an arm — which is why this is here and not at the one place a part
            // was known to go missing: every part the walk goes into is one a clause may have been
            // refused in, and the arm above it has been told how it is reached either way.
            return;
        }
        boolean arrives = observed && reading.arrivesAt(node);
        if (observed && !arrives && reach instanceof Reach.Ways(var ways)) {
            answersNothingAt(node, ways.stream().map(WayIn::conditions).toList());
        }
        if (node instanceof Core.LetIn let) {
            // A name given to a decision is still that decision, and a name given to a position is
            // still that position. Both environments widen here and neither answers the other's
            // question. Nothing about getting here changes: a binding is not a fork.
            walk(let.value(), naming, reach, arrives);
            walk(let.body(), naming.entering(new ScopeStep.Let(let)), reach, arrives);
            return;
        }
        if (arrives && !reach.ways().isEmpty()) {
            meetings.at(node, reach.ways().stream().map(WayIn::decisions).toList(), reading);
        }
        descend(node, naming, reach, arrives);
    }

    /**
     * That a run arriving at {@code node} by any of {@code ways} answers nothing.
     *
     * <p>Asked where the walk first finds a value not arriving, so what is recorded is the largest
     * such part: below it the walk goes on with nothing observed, and nothing further down is asked.
     * And asked of {@link NormalReturn} besides, which is the reading of whether an arm answers
     * anything that the rest of this compiler reads — a part the two disagree about is not said to
     * answer nothing.
     *
     * <p>Only where every way here is named, which is the caller's to have checked. A way in
     * nothing states, or one stated coarser than the fork it comes out of, is one a row cannot be
     * kept off, so it says nothing about which inputs reach this.
     */
    private void answersNothingAt(Core node, List<List<Condition>> ways) {
        if (ways.isEmpty()) {
            return;
        }
        if (answering == null) {
            answering = NormalReturn.ofBody(body);
        }
        if (answering.at(node)) {
            return;
        }
        answersNothing.add(new NothingAnsweredHere(ways, UnreachableReasons.said(node, answering)));
    }

    /**
     * That a run down arm {@code part} of {@code match}, reached under {@code reach}, answers
     * nothing — where the arm is one no run through is watched.
     *
     * <p>Such an arm has no way in a row can be steered along: a way in is what a run that came it
     * would be seen doing, and nothing records a run through an arm that answers nothing. What it
     * takes of the inputs is its case all the same, and that with what held on the way to the
     * {@code match} is what a row reaching it holds.
     */
    private void answersNothingDown(Core.Match match, int part, CoverageNaming naming,
                                    Reach reach) {
        if (!(reach instanceof Reach.Ways(var ways))) {
            return;
        }
        Condition.Case taken = naming.caseOf(match, part);
        if (taken == null) {
            return;
        }
        List<List<Condition>> down = new ArrayList<>();
        for (WayIn way : ways) {
            List<Condition> held = new ArrayList<>(way.conditions());
            held.add(taken);
            down.add(held);
        }
        answersNothingAt(match.cases().get(part).body(), down);
    }

    /**
     * Into each part that runs when this is evaluated, under what holds on the way into it.
     *
     * <p>Not the parts a node is built out of, which is a different question. What it takes to get
     * to a part differs per shape — an arm is reached by the fork coming out its way, a scrutinee
     * whenever the fork is, the right of an operator that stops early only where the left did not
     * settle the answer — and a part is not always reached at all: evaluating a block makes a
     * function rather than running its body.
     *
     * <p>Exhaustive and with no fallback. A node kind added to the IR has to be decided about here
     * rather than fall in with the ones every part of which is evaluated under the same conditions,
     * because that is the assumption this walk was making about all of them and it was wrong for
     * two.
     */
    private void descend(Core node, CoverageNaming naming, Reach reach, boolean observed) {
        switch (node) {
            case Core.If iff -> {
                walk(iff.cond(), naming, reach, observed);
                Core[] parts = {iff.then(), iff.els()};
                for (int part = 0; part < parts.length; part++) {
                    // As many ways in as the condition has of coming out that way, held to every
                    // context the fork itself is reached under: a row that failed the first
                    // comparison and one that held it and failed the second both arrive here, and
                    // they arrive by different paths.
                    Reach into = waysInTo(iff, part, naming, reach);
                    arms.at(iff, part, into, body);
                    walk(parts[part],
                            naming.entering(new ScopeStep.Chosen(
                                    Choice.Decides.ofCondition(iff, part == 0))),
                            into, observed);
                }
            }
            case Core.Match match -> {
                walk(match.scrutinee(), naming, reach, observed);
                for (int part = 0; part < match.cases().size(); part++) {
                    Outcome went = naming.matchCase(match, part);
                    // One way in and never more, so nothing here can go over the bound. A case the
                    // reading could not name is a way in nothing states, which is what is inside it
                    // as much as it is the arm itself.
                    Reach into = went == null
                            ? unnamed(reach, PathAccess.Unsupported.Why.NO_WAY_IN_CAN_BE_NAMED)
                            : under(reach, new Reach.Ways(List.of(new WayIn(went.holds()))));
                    if (went != null) {
                        takes(into, new Reach.Ways(List.of(new WayIn(went.holds()))));
                    } else if (observed && !reading.arrivesAt(match.cases().get(part).body())) {
                        answersNothingDown(match, part, naming, reach);
                    }
                    arms.at(match, part, into, body);
                    Core.Case arm = match.cases().get(part);
                    walk(arm.body(),
                            naming.entering(new ScopeStep.Chosen(
                                    Choice.Decides.ofCase(match, arm))),
                            into, observed);
                }
            }
            case Core.Binary binary when binary.op().stopsWhenItsAnswerIsSettled() -> {
                walk(binary.left(), naming, reach, observed);
                walk(binary.right(), naming, rightOf(binary, reach), observed);
            }
            case Core.IfConstructed constructed -> {
                // The values are made, and which arm is taken is whether making the thing out of
                // them held its rules. No class of an input names that, so a row cannot be steered
                // to either arm — and the arms are still arms, so what is in them is read under a
                // way in nothing states rather than not read at all. Inside `then` the attempt's
                // name stands for what was built, as it does to every reading of the input.
                for (Core.FieldValue given : constructed.construct().values()) {
                    walk(given.value(), naming, reach, observed);
                }
                Reach into = unnamed(reach,
                        PathAccess.Unsupported.Why.THE_CONSTRUCTION_DECIDES_IT);
                // And each arm is a way runs take all the same. Whether the rules held is a
                // decision about the values the thing was made of — a rule refusing a case refuses
                // it of whatever position the value came from — which nothing here can name, and
                // which a reading of what the body tells apart is owed.
                for (int arm = 0; arm <= constructed.els().size(); arm++) {
                    Outcome went = naming.forkArm(constructed, arm);
                    if (went != null) {
                        Reach own = new Reach.Ways(List.of(new WayIn(went.holds())));
                        takes(under(reach, own), own);
                    }
                }
                int part = 0;
                arms.at(constructed, part++, into, body);
                walk(constructed.then(),
                        naming.entering(new ScopeStep.Chosen(
                                Choice.Decides.ofBuilt(constructed))),
                        into, observed);
                for (Core.ElseArm departure : constructed.els()) {
                    arms.at(constructed, part++, into, body);
                    walk(departure.body(),
                            naming.entering(new ScopeStep.Chosen(
                                    Choice.Decides.ofDeparture(constructed, departure))),
                            into, observed);
                }
            }
            case Core.Block block -> {
                // Evaluating this makes the function; the body runs where something calls it, under
                // whatever it is called with. That is not a condition on the inputs of this
                // behavior, so nothing in there has a way in this can name — and the arms in there
                // are numbered like any others, so they are read and told that.
                walk(block.body(), naming.entering(new ScopeStep.Block(block)),
                        unnamed(reach, PathAccess.Unsupported.Why.RUNS_WHERE_SOMETHING_CALLS_IT),
                        observed);
            }
            case Core.LetIn let -> {
                walk(let.value(), naming, reach, observed);
                walk(let.body(), naming.entering(new ScopeStep.Let(let)), reach, observed);
            }
            case Core.Int _ -> { }
            case Core.Decimal _ -> { }
            case Core.Str _ -> { }
            case Core.Bool _ -> { }
            case Core.Temporal _ -> { }
            case Core.Read _ -> { }
            case Core.UnitValue _ -> { }
            case Core.OptionNone _ -> { }
            case Core.Unreachable _ -> { }
            // What a tree an analysis reads holds where a value is built. This reads the tree that
            // runs, which holds the value's method and a call of it.
            case Core.MaterialisedValue m -> throw new IllegalStateException(
                    "the tree that runs holds no build of a value, and this holds one of "
                            + m.value());
            // Everything the node is made of is evaluated, and under what the node itself was.
            case Core.Neg neg -> walkAll(some(neg.operand()), naming, reach, observed);
            case Core.FieldAccess access -> walkAll(some(access.target()), naming, reach, observed);
            // What reading a type's guarantees reaches a value by. The tree that runs reads a field
            // an access at a time.
            case Core.FieldProjection p -> throw p.unexpectedIn("the reading of what runs");
            case Core.TupleGet get -> walkAll(some(get.tuple()), naming, reach, observed);
            case Core.OptionSome option -> walkAll(some(option.value()), naming, reach, observed);
            case Core.Widen widen -> walkAll(some(widen.value()), naming, reach, observed);
            case Core.Binary binary ->
                    walkAll(some(binary.left(), binary.right()), naming, reach, observed);
            // The arguments, and then the method of the module the call runs, if it runs one. Read
            // later, as a body of its own, entered under what holds here.
            case Core.Call call -> {
                walkAll(call.args(), naming, reach, observed);
                run.invokedBy(call).ifPresent(method -> enters(method, reach, observed));
            }
            case Core.PreservedCall call -> walkAll(call.args(), naming, reach, observed);
            case Core.Apply apply -> walkAll(apply.args(), naming, reach, observed);
            case Core.ListLit list -> walkAll(list.elements(), naming, reach, observed);
            case Core.Tuple tuple -> walkAll(tuple.elements(), naming, reach, observed);
            case Core.Construct construct -> walkAll(
                    construct.values().stream().map(Core.FieldValue::value).toList(),
                    naming, reach, observed);
        }
    }

    private void walkAll(List<Core> parts, CoverageNaming naming, Reach reach, boolean observed) {
        for (Core each : parts) {
            walk(each, naming, reach, observed);
        }
    }

    /**
     * How the right of an operator that stops early is reached.
     *
     * <p>It runs only where the left did not settle the answer, and which of the left's paths those
     * are is which value each of them comes to. Where the reading cannot enumerate them there is no
     * way in to name: a way in it could name only some of says a row reaches here when it may not,
     * and there is no arm here to fall back on — what leads to the right of one of these is the left
     * having come out a way, and nothing records a value coming out a way.
     */
    private Reach rightOf(Core.Binary binary, Reach reach) {
        if (!(reading.waysTo(binary.left(), binary.op().rightRunsWhenLeftIs())
                instanceof Ways.Known<Outcome> through)) {
            return unnamed(reach, PathAccess.Unsupported.Why.WAYS_NOT_ENUMERABLE);
        }
        if (through.paths().isEmpty()) {
            return new Reach.Nothing(
                    PathAccess.Unreachable.Why.THE_CONDITION_NEVER_COMES_OUT_THAT_WAY);
        }
        List<WayIn> left = waysOf(through.paths());
        Reach into = under(reach, new Reach.Ways(left));
        takes(into, new Reach.Ways(left));
        return into.ways().size() > MOST_WAYS_IN
                ? new Reach.Unnameable(PathAccess.Unsupported.Why.MORE_WAYS_IN_THAN_ARE_READ)
                : into;
    }

    /**
     * The path contexts arm {@code part} is read under, each held to what already held above it.
     *
     * <p>Every way the condition comes out that way against every context the fork is reached
     * under, which is the number this position is read under and is where it is checked against
     * the bound. Counted here and nowhere else: this is the one place the contexts of a position
     * are all in hand at once.
     */
    private Reach waysInTo(Core.If iff, int part, CoverageNaming naming, Reach reach) {
        Reach own = waysInFor(iff, part, naming);
        Reach into = under(reach, own);
        takes(into, own);
        if (into.ways().size() <= MOST_WAYS_IN) {
            return into;
        }
        // Over the bound, and read the one way it was read before the ways in were told apart. The
        // fallback is one way in per context, so what comes back is no longer than what came in and
        // the bound holds by induction rather than by anything counted along the way. What an arm
        // under it is told is the limit, which is not what the fallback looks like from below.
        return under(reach, fallbackWayIn(iff, part, naming,
                PathAccess.Unsupported.Why.MORE_WAYS_IN_THAN_ARE_READ));
    }

    /**
     * The ways the condition comes out for arm {@code part}, or what this reading has instead.
     *
     * <p>The reach is no part of this. What the condition can come out as is a fact about the
     * condition, and holding it to what already held is the caller's, which the outcomes of a value
     * and the walk into an arm do differently.
     */
    private Reach waysInFor(Core.If iff, int part, CoverageNaming naming) {
        // Whether the arm is there at all is the reading of what the body does, and it is asked
        // first. An arm the condition never comes out the way of is no arm to walk into, and falling
        // back to naming it would offer whatever is inside it under a reach no run takes.
        if (!reading.comesAt(iff.cond()).mayCome(part == 0)) {
            return new Reach.Nothing(
                    PathAccess.Unreachable.Why.THE_CONDITION_NEVER_COMES_OUT_THAT_WAY);
        }
        if (reading.waysInto(iff, part) instanceof Ways.Known<Outcome> known) {
            return known.paths().isEmpty()
                    ? new Reach.Nothing(
                            PathAccess.Unreachable.Why.THE_CONDITION_NEVER_COMES_OUT_THAT_WAY)
                    : new Reach.Ways(waysOf(known.paths()));
        }
        return fallbackWayIn(iff, part, naming,
                PathAccess.Unsupported.Why.WAYS_NOT_ENUMERABLE);
    }

    /** The arm itself as the one way in, for a condition this reading cannot value, under the
     *  {@code why} that left it with this rather than with the ways. */
    private Reach fallbackWayIn(Core.If iff, int part, CoverageNaming naming,
                                PathAccess.Unsupported.Why why) {
        Outcome back = naming.forkArm(iff, part);
        return back == null
                ? new Reach.Unnameable(PathAccess.Unsupported.Why.NO_WAY_IN_CAN_BE_NAMED)
                : new Reach.Coarse(List.of(new WayIn(back.holds())), why);
    }

    /**
     * A way in nothing states, under {@code above}.
     *
     * <p>Held to what holds above like any other step. Where no run gets to the place this is
     * asked at, none gets past it either, and a way in nothing states made there afresh would say
     * that runs go on through it — which turns a proof that nothing arrives into a limit of this
     * reading, and lets whatever is decided further in be read as something the body does.
     */
    private static Reach unnamed(Reach above, PathAccess.Unsupported.Why why) {
        return under(above, new Reach.Unnameable(why));
    }

    /**
     * A step held to what already held above it.
     *
     * <p>What the two come to together, and which of them decides is what the order below says. A
     * step that shows nothing arrives is what it shows however little could be said about the way to
     * it — the condition never comes out that way whatever stands above — so it is asked first and a
     * context this reading had no words for does not swallow a proof about the body. Everything else
     * inherits: under a place nothing reaches, nothing reaches; under a way in nothing states, no
     * way in is stated.
     *
     * <p>A contradiction is read off the decisions themselves. Two of them settling one decision two
     * ways is no path whether either was named for a class or for the arm it takes, so nothing here
     * is inferred from a condition this reading could not state.
     */
    private static Reach under(Reach above, Reach step) {
        if (step instanceof Reach.Nothing) {
            return step;
        }
        if (above instanceof Reach.Nothing) {
            return above;
        }
        // A way in nothing states, above or here, and no way in is stated below it. What is known
        // goes on all the same: the step nothing states is taken to rule out nothing, and what was
        // named on either side of it still holds wherever a run is — which is what a reading of
        // what the body decides is held to, and what no row is steered by.
        if (above instanceof Reach.Unnameable || step instanceof Reach.Unnameable) {
            PathAccess.Unsupported.Why why = above instanceof Reach.Unnameable it ? it.why()
                    : ((Reach.Unnameable) step).why();
            List<WayIn> known = both(above.known(), step.known());
            if (known.isEmpty()) {
                return new Reach.Nothing(PathAccess.Unreachable.Why.CONTRADICTS_WHAT_ALREADY_HELD);
            }
            // Past the bound what is known is the step's own and nothing above it, which leaves what
            // a run here decided read against more than it was decided in, and never less — and
            // never drops what the step itself decided.
            return new Reach.Unnameable(why, known.size() > MOST_WAYS_IN ? step.known() : known);
        }
        List<WayIn> held = both(above.ways(), step.ways());
        if (held.isEmpty()) {
            return new Reach.Nothing(PathAccess.Unreachable.Why.CONTRADICTS_WHAT_ALREADY_HELD);
        }
        if (above instanceof Reach.Coarse(var _, var why)) {
            return new Reach.Coarse(held, why);
        }
        if (step instanceof Reach.Coarse(var _, var why)) {
            return new Reach.Coarse(held, why);
        }
        return new Reach.Ways(held);
    }

    /**
     * A place reached wherever {@code one} or {@code other} reaches it.
     *
     * <p>Every way of either, which is no more than the ways there are. What either could not name
     * stays unnamed: a way in nothing states on one side is a run arriving that no row can be
     * steered along, and the ways of the other side do not say how it got there. Past the bound the
     * ways are read no further, and neither is what is known on them.
     */
    private static Reach either(Reach one, Reach other) {
        if (other instanceof Reach.Nothing) {
            return one;
        }
        if (one instanceof Reach.Nothing) {
            return other;
        }
        if (one instanceof Reach.Unnameable || other instanceof Reach.Unnameable) {
            PathAccess.Unsupported.Why why = one instanceof Reach.Unnameable it ? it.why()
                    : ((Reach.Unnameable) other).why();
            List<WayIn> known = anyOf(one.known(), other.known());
            return known.size() > MOST_WAYS_IN ? new Reach.Unnameable(why)
                    : new Reach.Unnameable(why, known);
        }
        List<WayIn> ways = anyOf(one.ways(), other.ways());
        if (ways.size() > MOST_WAYS_IN) {
            return new Reach.Unnameable(PathAccess.Unsupported.Why.MORE_WAYS_IN_THAN_ARE_READ);
        }
        if (one instanceof Reach.Coarse(var _, var why)) {
            return new Reach.Coarse(ways, why);
        }
        if (other instanceof Reach.Coarse(var _, var why)) {
            return new Reach.Coarse(ways, why);
        }
        return new Reach.Ways(ways);
    }

    /** The ways of both, each once. */
    private static List<WayIn> anyOf(List<WayIn> one, List<WayIn> other) {
        Set<WayIn> out = new LinkedHashSet<>(one);
        out.addAll(other);
        return List.copyOf(out);
    }

    /** Every way of {@code above} with every way of {@code step}, leaving out the ones that settle
     *  one decision both ways. */
    private static List<WayIn> both(List<WayIn> above, List<WayIn> step) {
        List<WayIn> held = new ArrayList<>();
        for (WayIn reach : above) {
            for (WayIn way : step) {
                List<Decision> merged = CoverageNaming.merge(reach.decisions(), way.decisions());
                if (merged != null) {
                    held.add(new WayIn(merged));
                }
            }
        }
        return held;
    }

    /** The ways, as the conjunctions they are. */
    private static List<WayIn> waysOf(List<Outcome> ways) {
        return ways.stream().map(each -> new WayIn(each.holds())).toList();
    }

    /**
     * The parts of a node that are there.
     *
     * <p>A body the checker refused a clause of arrives with a hole where the clause was, and a
     * reading that is not the checker has nothing to say about it: what is missing is missing, and
     * the decisions either side of it are still decisions. Used where the parts are walked and not
     * where they are numbered — an arm's place among the arms is what says which way the fork came
     * out, and a list with the missing one taken out would call the second arm the first.
     */
    private static List<Core> some(Core... parts) {
        List<Core> out = new ArrayList<>();
        for (Core each : parts) {
            if (each != null) {
                out.add(each);
            }
        }
        return out;
    }
}
