package souther.compiler.interaction;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.flow.ValueArrivals;
import souther.compiler.flow.Ways;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.List;

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
 * together. A reading given its own walk would be a second reading of the same body, free to
 * disagree with this one the day either of them moves — which is how a fact came to be spelled twice
 * before. So what is shared here is where the walk goes and what holds there; what is found is each
 * collector's own, and so is the state finding it needs.
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
     * for no more than was asked for then.
     */
    private static final int MOST_WAYS_IN = 16;

    /** What the body was read to arrive at, and by which ways. Read once, before the walk starts. */
    private final ValueArrivals<Outcome> reading;

    /** The meetings this walk is read for. One of the collectors the walk feeds, and the owner of
     *  everything finding a meeting takes. */
    private final Meetings meetings;

    private CoverageRead(ValueArrivals<Outcome> reading, Meetings meetings) {
        this.reading = reading;
        this.meetings = meetings;
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
     */
    public record Read(List<Interaction> interactions) {

        public Read {
            interactions = List.copyOf(interactions);
        }
    }

    /** What the walk over {@code body} reads. */
    public static Read of(Core body, CoverageSites.Plan plan, InputDomain inputs,
                          Symbols symbols) {
        CoverageNaming naming = new CoverageNaming(plan, symbols, InputReads.of(inputs));
        ValueArrivals<Outcome> reading = ValueArrivals.ofBody(body, naming);
        Meetings meetings = new Meetings(plan, reading);
        new CoverageRead(reading, meetings).walk(body, naming, List.of(List.of()));
        return new Read(meetings.found());
    }

    /**
     * @param reaches every way in this position is reached by, together rather than one at a time,
     *                because how many there are is what {@link #MOST_WAYS_IN} bounds and no one of
     *                them can say. Empty where nothing reaches here, and never longer than the bound
     */
    private void walk(Core node, CoverageNaming naming, List<List<Decision>> reaches) {
        if (reaches.isEmpty()) {
            // Every way that would have led here settles a decision one of the ways above it
            // settled the other way, so no run arrives and there is nothing in here to offer.
            return;
        }
        if (!reading.arrivesAt(node)) {
            // The same invariant the outcomes are read under, and the walk is where it is decided
            // whether there is a group here at all. A subtree that arrives at no value is one no
            // row observes: the decisions inside an arm that aborts are made and then thrown away
            // with the run, so a group found in there would be offered rows that settle nothing.
            // A part that is not there — the hole a refused clause leaves — answers nothing either
            // and stops the walk the same way.
            return;
        }
        if (node instanceof Core.LetIn let) {
            // A name given to a decision is still that decision, and a name given to a position is
            // still that position. Both environments widen here and neither answers the other's
            // question. Nothing about getting here changes: a binding is not a fork.
            walk(let.value(), naming, reaches);
            walk(let.body(), naming.under(let.binder(), let.value()), reaches);
            return;
        }
        meetings.at(node, reaches);
        descend(node, naming, reaches);
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
    private void descend(Core node, CoverageNaming naming, List<List<Decision>> reaches) {
        switch (node) {
            // A way in nobody can name stops the walk into that arm, whether what could not be named
            // is the position the decision is about or the place a run that took it would be seen at.
            // A group found in there would be under a condition nothing can steer a row into or hold
            // a run to, and offering it asks for a row that may never arrive.
            case Core.If iff -> {
                walk(iff.cond(), naming, reaches);
                Core[] arms = {iff.then(), iff.els()};
                for (int part = 0; part < arms.length; part++) {
                    // As many ways in as the condition has of coming out that way, held to every
                    // context the fork itself is reached under: a row that failed the first
                    // comparison and one that held it and failed the second both arrive here, and
                    // they arrive by different paths.
                    walk(arms[part], naming, waysInTo(iff, part, naming, reaches));
                }
            }
            case Core.Match match -> {
                walk(match.scrutinee(), naming, reaches);
                for (int part = 0; part < match.cases().size(); part++) {
                    Outcome went = naming.matchCase(match, part);
                    if (went == null) {
                        continue;
                    }
                    // One way in and never more, so nothing here can go over the bound.
                    walk(match.cases().get(part).body(), naming,
                            heldTo(reaches, List.of(went.holds())));
                }
            }
            case Core.Binary binary when binary.op().stopsWhenItsAnswerIsSettled() -> {
                walk(binary.left(), naming, reaches);
                // The right runs only where the left did not settle the answer, and which of the
                // left's paths those are is which value each of them comes to. Where the reading
                // cannot enumerate them the walk does not go in: a way in it could name only some
                // of says a row reaches here when it may not.
                //
                // Over the bound the walk does not go in either. There is no arm here to fall back
                // on — what leads to the right of one of these is the left having come out a way,
                // and nothing records a value coming out a way.
                if (reading.waysTo(binary.left(), binary.op().rightRunsWhenLeftIs())
                        instanceof Ways.Known<Outcome> through) {
                    List<List<Decision>> ways = heldTo(reaches, holdsOf(through.paths()));
                    if (ways.size() <= MOST_WAYS_IN) {
                        walk(binary.right(), naming, ways);
                    }
                }
            }
            case Core.IfConstructed constructed -> {
                // The values are made, and which arm is taken is whether making the thing out of
                // them held its rules. No class of an input names that, so what is inside the arms
                // is not walked: a row cannot be steered to either of them, and one offered for a
                // group in there would be offered for a combination it may not sit in.
                for (Core.FieldValue given : constructed.construct().values()) {
                    walk(given.value(), naming, reaches);
                }
            }
            case Core.Block ignored -> {
                // Evaluating this makes the function; the body runs where something calls it, under
                // whatever it is called with. That is not a condition on the inputs of this
                // behavior, so a group in there has no way in this can name.
            }
            case Core.LetIn let -> {
                walk(let.value(), naming, reaches);
                walk(let.body(), naming.under(let.binder(), let.value()), reaches);
            }
            case Core.Int ignored -> { }
            case Core.Decimal ignored -> { }
            case Core.Str ignored -> { }
            case Core.Bool ignored -> { }
            case Core.Temporal ignored -> { }
            case Core.Read ignored -> { }
            case Core.UnitValue ignored -> { }
            case Core.OptionNone ignored -> { }
            case Core.Unreachable ignored -> { }
            // Everything the node is made of is evaluated, and under what the node itself was.
            case Core.Neg neg -> walkAll(some(neg.operand()), naming, reaches);
            case Core.FieldAccess access -> walkAll(some(access.target()), naming, reaches);
            case Core.TupleGet get -> walkAll(some(get.tuple()), naming, reaches);
            case Core.OptionSome option -> walkAll(some(option.value()), naming, reaches);
            case Core.Binary binary ->
                    walkAll(some(binary.left(), binary.right()), naming, reaches);
            case Core.Call call -> walkAll(call.args(), naming, reaches);
            case Core.PreservedCall call -> walkAll(call.args(), naming, reaches);
            case Core.Apply apply -> walkAll(apply.args(), naming, reaches);
            case Core.ListLit list -> walkAll(list.elements(), naming, reaches);
            case Core.Tuple tuple -> walkAll(tuple.elements(), naming, reaches);
            case Core.Construct construct -> walkAll(
                    construct.values().stream().map(Core.FieldValue::value).toList(),
                    naming, reaches);
        }
    }

    private void walkAll(List<Core> parts, CoverageNaming naming, List<List<Decision>> reaches) {
        for (Core each : parts) {
            walk(each, naming, reaches);
        }
    }

    /**
     * The path contexts arm {@code part} is read under, each held to what already held above it.
     *
     * <p>Every way the condition comes out that way against every context the fork is reached
     * under, which is the number this position is read under and is where it is checked against
     * the bound. Counted here and nowhere else: this is the one place the contexts of a position
     * are all in hand at once.
     *
     * <p>Empty where no row reaches the arm at all, which is a different answer from the one way in
     * this falls back to where the condition's ways cannot be enumerated — and a different answer
     * again from the arm having no way in that can be named, which is also empty and is where the
     * walk stops for the reason it always did.
     */
    private List<List<Decision>> waysInTo(Core.If iff, int part, CoverageNaming naming,
                                          List<List<Decision>> reaches) {
        List<List<Decision>> ways = heldTo(reaches, waysInFor(iff, part, naming));
        if (ways.size() <= MOST_WAYS_IN) {
            return ways;
        }
        // Over the bound, and read the one way it was read before the ways in were told apart. The
        // fallback is one way in per context, so what comes back is no longer than what came in and
        // the bound holds by induction rather than by anything counted along the way.
        return heldTo(reaches, fallbackWayIn(iff, part, naming));
    }

    /**
     * The ways the condition comes out for arm {@code part}, or the arm itself where it cannot say.
     *
     * <p>The reach is no part of this. What the condition can come out as is a fact about the
     * condition, and holding it to what already held is the caller's, which the outcomes of a value
     * and the walk into an arm do differently.
     */
    private List<List<Decision>> waysInFor(Core.If iff, int part, CoverageNaming naming) {
        // Whether the arm is there at all is the reading of what the body does, and it is asked
        // first. An arm the condition never comes out the way of is no arm to walk into, and falling
        // back to naming it would offer whatever is inside it under a reach no run takes.
        if (!reading.comesAt(iff.cond()).mayCome(part == 0)) {
            return List.of();
        }
        if (reading.waysTo(iff.cond(), part == 0) instanceof Ways.Known<Outcome> known) {
            return holdsOf(known.paths());
        }
        return fallbackWayIn(iff, part, naming);
    }

    /** The arm itself as the one way in, for a condition this reading cannot value. */
    private List<List<Decision>> fallbackWayIn(Core.If iff, int part, CoverageNaming naming) {
        Outcome back = naming.forkArm(iff, part);
        return back == null ? List.of() : List.of(back.holds());
    }

    /**
     * Each way in held to each context it is reached under, leaving out the ones that contradict.
     *
     * <p>Where the ways in are counted from. A way settling a decision that the context it would
     * extend settled the other way is no path, so it is not here — and a bound taken over what is
     * here is a bound on paths rather than on what the syntax offered.
     */
    private static List<List<Decision>> heldTo(List<List<Decision>> reaches,
                                               List<List<Decision>> ways) {
        List<List<Decision>> out = new ArrayList<>();
        for (List<Decision> reach : reaches) {
            for (List<Decision> way : ways) {
                List<Decision> merged = CoverageNaming.merge(reach, way);
                if (merged != null) {
                    out.add(merged);
                }
            }
        }
        return out;
    }

    /** The conditions of each way, which is what the walk carries a reach as. */
    private static List<List<Decision>> holdsOf(List<Outcome> ways) {
        return ways.stream().map(Outcome::holds).toList();
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
