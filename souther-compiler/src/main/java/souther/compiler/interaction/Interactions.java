package souther.compiler.interaction;

import souther.compiler.ast.Hir;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.flow.Arrival;
import souther.compiler.flow.ValueArrivals;
import souther.compiler.flow.Ways;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

/**
 * Which decisions of a behavior's body determine one value together.
 *
 * <p>Nothing else reads this. Every measure over a body reads control flow — which arms were
 * entered — and passing through all four arms of {@code if A { if B { X } else { Y } } else { Z }}
 * says nothing about whether the interactions between A and B were tried. This reads what a value
 * owes itself to instead, which is the question a combination is about.
 *
 * <p>A node with several children is not a meeting. Under
 * {@code Order { price = if A then 100 else 200, message = if B then "x" else "y" }} the two
 * decisions arrive at a constructor and interact in nothing, because no observation is a function
 * of both. A group forms only where two values each settled by a decision are consumed into one:
 * an operand of an operator, or an argument of a call that answers one value.
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

public final class Interactions {

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

    private final CoverageSites.Plan plan;

    /** What the body was read to arrive at, and by which ways. Read once, before the walk starts. */
    private final ValueArrivals<Outcome> reading;

    private Interactions(CoverageSites.Plan plan, ValueArrivals<Outcome> reading) {
        this.plan = plan;
        this.reading = reading;
    }

    /**
     * The groups of {@code body}, in the order the walk meets them.
     *
     * <p>By the meeting first and by the way in second. A meeting reached several ways is one place
     * in the body and as many groups, and they are written down together because that is when the
     * walk is there. A generation spending a row budget over these takes them in this order, so
     * which of them a budget that runs out reaches is said by where the meeting is written and not
     * by which way round a fork above it a row goes.
     */
    public static List<Interaction> of(Core body, CoverageSites.Plan plan, InputDomain inputs,
                                       Symbols symbols) {
        List<Interaction> found = new ArrayList<>();
        CoverageNaming naming = new CoverageNaming(plan, symbols, InputReads.of(inputs));
        new Interactions(plan, ValueArrivals.ofBody(body, naming))
                .walk(body, naming, java.util.Collections.newSetFromMap(new IdentityHashMap<>()),
                        List.of(List.of()), found);
        return List.copyOf(found);
    }


    /**
     * @param reaches every way in this position is reached by, together rather than one at a time,
     *                because how many there are is what {@link #MOST_WAYS_IN} bounds and no one of
     *                them can say. Empty where nothing reaches here, and never longer than the bound
     */
    private void walk(Core node, CoverageNaming naming, Set<Core> absorbed,
                      List<List<Decision>> reaches, List<Interaction> found) {
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
            walk(let.value(), naming, absorbed, reaches, found);
            walk(let.body(), naming.under(let.binder(), let.value()), absorbed, reaches, found);
            return;
        }
        List<Core> meeting = absorbed.contains(node) ? null : meetingAt(node, absorbed);
        if (meeting != null) {
            List<Factor> factors = new ArrayList<>();
            for (Core operand : meeting) {
                List<Outcome> outcomes = outcomesOf(operand);
                // One outcome is no decision: the operand answers the same way however the row is
                // written, so nothing about it can be varied against the other operand.
                if (outcomes.size() > 1) {
                    factors.add(new Factor(outcomes));
                }
            }
            // A group says that these decisions were settled these ways and met here, which is a
            // statement about one passing. What can be established about a run is what its recording
            // holds, and that is which places it passed rather than how many times it passed each —
            // so where a run may come back to this meeting, the two factors coming out the named
            // ways is not something any reading of such a recording can tell from their coming out
            // those ways on different times round. The group would be one nothing could ever show a
            // row to sit in, so it is not offered.
            //
            // Asked at the meeting and nowhere else, which is enough because a place a run may come
            // back to has everything inside it in the same position: a meeting this is false of
            // names a way in and factors that are all false of it too.
            //
            // What varies here is read once and the ways in are as many as they are: an operand is
            // settled the same ways whichever way round the forks above a row went, so the factors
            // are no part of what a way in decides and are not read again per way.
            if (factors.size() > 1 && !plan.mayRepeat(node)) {
                for (List<Decision> reach : reaches) {
                    found.add(new Interaction(reach, factors));
                }
            }
        }
        descend(node, naming, absorbed, reaches, found);
    }


    /**
     * Into each part that runs when this is evaluated, under what holds on the way into it.
     *
     * <p>Not the parts a node is built out of, which is {@link #childrenOf}'s answer and a
     * different question. What it takes to get to a part differs per shape — an arm is reached by
     * the fork coming out its way, a scrutinee whenever the fork is, the right of an operator that
     * stops early only where the left did not settle the answer — and a part is not always reached
     * at all: evaluating a block makes a function rather than running its body.
     *
     * <p>Exhaustive and with no fallback. A node kind added to the IR has to be decided about here
     * rather than fall in with the ones every part of which is evaluated under the same conditions,
     * because that is the assumption this walk was making about all of them and it was wrong for
     * two.
     */
    private void descend(Core node, CoverageNaming naming, Set<Core> absorbed,
                         List<List<Decision>> reaches, List<Interaction> found) {
        switch (node) {
            // A way in nobody can name stops the walk into that arm, whether what could not be named
            // is the position the decision is about or the place a run that took it would be seen at.
            // A group found in there would be under a condition nothing can steer a row into or hold
            // a run to, and offering it asks for a row that may never arrive.
            case Core.If iff -> {
                walk(iff.cond(), naming, absorbed, reaches, found);
                Core[] arms = {iff.then(), iff.els()};
                for (int part = 0; part < arms.length; part++) {
                    // As many ways in as the condition has of coming out that way, held to every
                    // context the fork itself is reached under: a row that failed the first
                    // comparison and one that held it and failed the second both arrive here, and
                    // they arrive by different paths.
                    walk(arms[part], naming, absorbed,
                            waysInTo(iff, part, naming, reaches), found);
                }
            }
            case Core.Match match -> {
                walk(match.scrutinee(), naming, absorbed, reaches, found);
                for (int part = 0; part < match.cases().size(); part++) {
                    Outcome went = naming.matchCase(match, part);
                    if (went == null) {
                        continue;
                    }
                    // One way in and never more, so nothing here can go over the bound.
                    walk(match.cases().get(part).body(), naming, absorbed,
                            heldTo(reaches, List.of(went.holds())), found);
                }
            }
            case Core.Binary binary when ValueArrivals.shortCircuits(binary.op()) -> {
                walk(binary.left(), naming, absorbed, reaches, found);
                // The right runs only where the left did not settle the answer, and which of the
                // left's paths those are is which value each of them comes to. Where the reading
                // cannot enumerate them the walk does not go in: a way in it could name only some
                // of says a row reaches here when it may not.
                //
                // Over the bound the walk does not go in either. There is no arm here to fall back
                // on — what leads to the right of one of these is the left having come out a way,
                // and nothing records a value coming out a way.
                if (reading.waysTo(binary.left(), binary.op() == Hir.BinOp.AND)
                        instanceof Ways.Known<Outcome> through) {
                    List<List<Decision>> ways = heldTo(reaches, holdsOf(through.paths()));
                    if (ways.size() <= MOST_WAYS_IN) {
                        walk(binary.right(), naming, absorbed, ways, found);
                    }
                }
            }
            case Core.IfConstructed constructed -> {
                // The values are made, and which arm is taken is whether making the thing out of
                // them held its rules. No class of an input names that, so what is inside the arms
                // is not walked: a row cannot be steered to either of them, and one offered for a
                // group in there would be offered for a combination it may not sit in.
                for (Core.FieldValue given : constructed.construct().values()) {
                    walk(given.value(), naming, absorbed, reaches, found);
                }
            }
            case Core.Block ignored -> {
                // Evaluating this makes the function; the body runs where something calls it, under
                // whatever it is called with. That is not a condition on the inputs of this
                // behavior, so a group in there has no way in this can name.
            }
            case Core.LetIn let -> {
                walk(let.value(), naming, absorbed, reaches, found);
                walk(let.body(), naming.under(let.binder(), let.value()), absorbed, reaches, found);
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
            case Core.Neg neg ->
                    walkAll(some(neg.operand()), naming, absorbed, reaches, found);
            case Core.FieldAccess access ->
                    walkAll(some(access.target()), naming, absorbed, reaches, found);
            case Core.TupleGet get ->
                    walkAll(some(get.tuple()), naming, absorbed, reaches, found);
            case Core.OptionSome option ->
                    walkAll(some(option.value()), naming, absorbed, reaches, found);
            case Core.Binary binary -> walkAll(some(binary.left(), binary.right()), naming, absorbed,
                    reaches, found);
            case Core.Call call ->
                    walkAll(call.args(), naming, absorbed, reaches, found);
            case Core.PreservedCall call ->
                    walkAll(call.args(), naming, absorbed, reaches, found);
            case Core.Apply apply ->
                    walkAll(apply.args(), naming, absorbed, reaches, found);
            case Core.ListLit list ->
                    walkAll(list.elements(), naming, absorbed, reaches, found);
            case Core.Tuple tuple ->
                    walkAll(tuple.elements(), naming, absorbed, reaches, found);
            case Core.Construct construct -> walkAll(
                    construct.values().stream().map(Core.FieldValue::value).toList(),
                    naming, absorbed, reaches, found);
        }
    }

    private void walkAll(List<Core> parts, CoverageNaming naming, Set<Core> absorbed,
                         List<List<Decision>> reaches, List<Interaction> found) {
        for (Core each : parts) {
            walk(each, naming, absorbed, reaches, found);
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
     * The ways {@code e} can be settled that a group can be composed against.
     *
     * <p>A projection of the reading and not a second walk. Two ways written down the same are one
     * way: a value settled twice over by the reading getting there twice is settled once, and a
     * factor counting the second would report a value varying where it does not.
     *
     * <p>A way the naming could not write down whole is not one of these. What a factor offers is a
     * combination a row is steered into, and the conditions of such a way do not say what would
     * steer one there — so it is left out, and where that leaves none the value is answered as
     * varying in no way this can compose against rather than as varying in one nobody can reach.
     */
    private List<Outcome> outcomesOf(Core e) {
        List<Outcome> out = new ArrayList<>();
        for (Arrival<Outcome> each : reading.at(e)) {
            if (each.isComplete() && !out.contains(each.path())) {
                out.add(each.path());
            }
        }
        return out;
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

    /**
     * The values consumed into one here, or null where this node consumes none.
     *
     * <p>A run of one operator is one meeting. {@code a + b + c} is written as one operator applied
     * twice and is three values making one, so reading it as two meetings would ask for the product
     * of the left two against the third and then again for the product of the first two — the
     * second being a projection of the first, and every row of it a row the first already wanted.
     * The nodes taken into the run are recorded so the walk does not meet them again.
     */
    private static List<Core> meetingAt(Core node, Set<Core> absorbed) {
        return switch (node) {
            case Core.Binary binary when ValueArrivals.shortCircuits(binary.op()) -> null;
            case Core.Binary binary -> {
                List<Core> operands = new ArrayList<>();
                List<Core> inner = new ArrayList<>();
                run(binary.left(), binary.op(), operands, inner);
                run(binary.right(), binary.op(), operands, inner);
                if (operands.size() < 2) {
                    yield null;
                }
                absorbed.addAll(inner);
                yield operands;
            }
            case Core.Call call -> call.args().size() > 1 ? call.args() : null;
            case Core.PreservedCall call -> call.args().size() > 1 ? call.args() : null;
            case Core.Apply apply -> apply.args().size() > 1 ? apply.args() : null;
            default -> null;
        };
    }

    /** The values one run of {@code op} is over, and the nodes the run is written as. */
    private static void run(Core e, Hir.BinOp op, List<Core> operands, List<Core> inner) {
        if (e instanceof Core.Binary binary && binary.op() == op) {
            inner.add(binary);
            run(binary.left(), op, operands, inner);
            run(binary.right(), op, operands, inner);
        } else if (e != null) {
            operands.add(e);
        }
    }
}
