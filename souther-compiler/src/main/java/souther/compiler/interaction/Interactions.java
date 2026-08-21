package souther.compiler.interaction;

import souther.compiler.ast.Hir;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.NormalReturn;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
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
 * <p>A path to a value and what the value is are two questions, and this answers both. The second is
 * about the reading rather than about the body and is what an operator stopping as soon as its
 * answer is settled turns on: which of its left's paths go on to the right is which value each of
 * them comes to. Answered by the same walk that answers the first, because two walks over one tree
 * are two answers that have to agree and one place for them to stop agreeing.
 *
 * <p>Under-reading is the safe direction. A group nothing formed is an obligation nobody is asked
 * for, which is where a product over the input positions already leaves things; a group formed too
 * eagerly asks for rows that establish nothing. Both limits below take that direction: a value that
 * can be settled more ways than the reading will tell apart is answered as settled one way, and a
 * position reached more ways than it will read at once is read the one way it used to be.
 */
public final class Interactions {

    /**
     * How many ways one value may be settled before the reading stops telling them apart.
     *
     * <p>A value built out of several is settled every way its parts are settled together, so a
     * record of fifteen independently forked fields has thirty-two thousand of them and every
     * enclosing operator would fold over all of them again. What is measurable before the work is
     * the size of the product as it is taken, so that is what is bounded — and a value over the
     * bound is answered as settled one way, which asks for nothing rather than asking for a number
     * of rows nobody would read.
     */
    private static final int MOST_OUTCOMES = 64;

    /**
     * How many path contexts one position of the body will be read under.
     *
     * <p>A second amplification and not the one above. {@link #MOST_OUTCOMES} bounds the outcomes
     * of one value, which is a product taken at one node; this bounds how many ways in one position
     * is walked under, which is a product taken along the way down to it. A condition that fails
     * four ways standing inside another one is a meeting read sixteen times, so the two multiply
     * with the nesting of the body and neither bound holds what the other does.
     *
     * <p>What is counted is the contexts that survive and not the alternatives the syntax offers. A
     * way in settling a decision that the way in above it settled the other way is no path at all,
     * and letting it take a share here would move where the bound falls with how the body is
     * written rather than with how much there is to read.
     *
     * <p>Over the bound an arm is read the one way a fork whose condition this reading cannot value
     * is read, which is where every fork was before the ways in were told apart. Going over asks
     * for no more than was asked for then.
     */
    private static final int MOST_WAYS_IN = 16;

    private final CoverageSites.Plan plan;
    private final Symbols symbols;

    /**
     * What each node was settled by, so an enclosing meeting does not fold over it again.
     *
     * <p>Keyed by identity and sound because a node occurs once: what is in scope at it is what the
     * walk had when it got there, so the environments are a function of the position and not a
     * second key.
     */
    private final IdentityHashMap<Core, List<Arrival>> settled = new IdentityHashMap<>();

    /**
     * A path to a value, and what this reading knows the value at the end of it to be.
     *
     * <p>Two questions, and the second is about the reading rather than about the body. An operator
     * that stops as soon as its answer is settled needs it: which of the left's paths go on to the
     * right is which value each of them comes to, and a reading holding conditions alone has no way
     * to ask.
     *
     * @param by         the conditions that hold along the path, which is what {@link Outcome} is
     * @param knownTruth what the value is, where this reading can say
     */
    private record Arrival(Outcome by, Truth knownTruth) { }

    /**
     * What this reading knows a path's value to be.
     *
     * <p>{@link #UNKNOWN} is not a third truth and not a path that arrives nowhere. The path is
     * there and it comes to a value; what is missing is this reading's answer for which of the two
     * it came to. A value nothing here forks arrives just as much as one it does.
     */
    private enum Truth { TRUE, FALSE, UNKNOWN }

    /**
     * The ways a value is settled to one truth, or that this reading cannot enumerate them.
     *
     * <p>All of them or none of them, and the type is what holds it to that. A list with paths
     * missing from it reads as a whole one: what takes it will steer no row down the paths it does
     * not hold and offer no group under them, which is the reading saying the body has not got them.
     * So one arrival whose truth is unread makes the whole enumeration {@link Unknown} rather than
     * quietly dropping itself out of a {@link Known} one.
     *
     * <p>{@code Known} holding nothing is an answer and not an absence. It says the value is never
     * settled that way, which is how an arm no row reaches is told from an arm this reading has
     * nothing to say about — the first is not walked and the second is walked under the arm itself.
     */
    private sealed interface Ways {

        /** These paths to that truth, and no others. */
        record Known(List<List<Decision>> paths) implements Ways { }

        /** Which paths come to that truth is not something this reading can say. */
        record Unknown() implements Ways { }
    }

    /** Which nodes are paths to a value, for the same reason the settlings are kept. */
    private final IdentityHashMap<Core, Boolean> reaches = new IdentityHashMap<>();

    private Interactions(CoverageSites.Plan plan, Symbols symbols) {
        this.plan = plan;
        this.symbols = symbols;
    }

    /** The groups of {@code body}, in the order the walk meets them. */
    public static List<Interaction> of(Core body, CoverageSites.Plan plan, InputDomain inputs,
                                       Symbols symbols) {
        List<Interaction> found = new ArrayList<>();
        new Interactions(plan, symbols).walk(body, InputReads.of(inputs), Map.of(),
                java.util.Collections.newSetFromMap(new IdentityHashMap<>()), List.of(), found, 1);
        return List.copyOf(found);
    }

    /**
     * @param contexts how many ways in this position is being read under, which is the product of
     *                 the ways the walk took to get here and is what {@link #MOST_WAYS_IN} bounds
     */
    private void walk(Core node, InputReads reads, Map<BindingId, List<Arrival>> bound,
                      Set<Core> absorbed, List<Decision> reach, List<Interaction> found,
                      int contexts) {
        if (!answers(node)) {
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
            walk(let.value(), reads, bound, absorbed, reach, found, contexts);
            Map<BindingId, List<Arrival>> inner = new HashMap<>(bound);
            inner.put(let.binder().binding(), arrivalsOf(let.value(), reads, bound));
            walk(let.body(), reads.and(let.binder(), let.value()), inner, absorbed, reach, found,
                    contexts);
            return;
        }
        List<Core> meeting = absorbed.contains(node) ? null : meetingAt(node, absorbed);
        if (meeting != null) {
            List<Factor> factors = new ArrayList<>();
            for (Core operand : meeting) {
                List<Outcome> outcomes = outcomesOf(operand, reads, bound);
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
            if (factors.size() > 1 && !plan.mayRepeat(node)) {
                found.add(new Interaction(reach, factors));
            }
        }
        descend(node, reads, bound, absorbed, reach, found, contexts);
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
    private void descend(Core node, InputReads reads, Map<BindingId, List<Arrival>> bound,
                         Set<Core> absorbed, List<Decision> reach, List<Interaction> found,
                         int contexts) {
        switch (node) {
            // A way in nobody can name stops the walk into that arm, whether what could not be named
            // is the position the decision is about or the place a run that took it would be seen at.
            // A group found in there would be under a condition nothing can steer a row into or hold
            // a run to, and offering it asks for a row that may never arrive.
            case Core.If iff -> {
                walk(iff.cond(), reads, bound, absorbed, reach, found, contexts);
                Core[] arms = {iff.then(), iff.els()};
                for (int part = 0; part < arms.length; part++) {
                    // As many ways in as the condition has of coming out that way, and the arm is
                    // read under each: a row that failed the first comparison and one that held it
                    // and failed the second both arrive here, and they arrive by different paths.
                    List<List<Decision>> ways = waysInTo(iff, part, reads, bound, reach, contexts);
                    for (List<Decision> way : ways) {
                        walk(arms[part], reads, bound, absorbed, way, found,
                                contexts * ways.size());
                    }
                }
            }
            case Core.Match match -> {
                TermPath at = reads.pathOf(match.scrutinee(), symbols);
                walk(match.scrutinee(), reads, bound, absorbed, reach, found, contexts);
                for (int part = 0; part < match.cases().size(); part++) {
                    Core.Case each = match.cases().get(part);
                    Decision went = caseCondition(at, each, match, part);
                    if (went == null) {
                        continue;
                    }
                    List<Decision> way = merge(reach, List.of(went));
                    if (way != null) {
                        walk(each.body(), reads, bound, absorbed, way, found, contexts);
                    }
                }
            }
            case Core.Binary binary when shortCircuits(binary.op()) -> {
                walk(binary.left(), reads, bound, absorbed, reach, found, contexts);
                // The right runs only where the left did not settle the answer, and which of the
                // left's paths those are is which value each of them comes to. Where the reading
                // cannot enumerate them the walk does not go in: a way in it could name only some
                // of says a row reaches here when it may not.
                if (waysTo(binary.left(), binary.op() == Hir.BinOp.AND, reads, bound)
                        instanceof Ways.Known through) {
                    List<List<Decision>> ways = compatible(reach, through.paths());
                    if (contexts * ways.size() <= MOST_WAYS_IN) {
                        for (List<Decision> way : ways) {
                            walk(binary.right(), reads, bound, absorbed, way, found,
                                    contexts * ways.size());
                        }
                    }
                }
            }
            case Core.IfConstructed constructed -> {
                // The values are made, and which arm is taken is whether making the thing out of
                // them held its rules. No class of an input names that, so what is inside the arms
                // is not walked: a row cannot be steered to either of them, and one offered for a
                // group in there would be offered for a combination it may not sit in.
                for (Core.FieldValue given : constructed.construct().values()) {
                    walk(given.value(), reads, bound, absorbed, reach, found, contexts);
                }
            }
            case Core.Block ignored -> {
                // Evaluating this makes the function; the body runs where something calls it, under
                // whatever it is called with. That is not a condition on the inputs of this
                // behavior, so a group in there has no way in this can name.
            }
            case Core.LetIn let -> {
                walk(let.value(), reads, bound, absorbed, reach, found, contexts);
                walk(let.body(), reads.and(let.binder(), let.value()), bound, absorbed, reach,
                        found, contexts);
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
                    walkAll(some(neg.operand()), reads, bound, absorbed, reach, found, contexts);
            case Core.FieldAccess access ->
                    walkAll(some(access.target()), reads, bound, absorbed, reach, found, contexts);
            case Core.TupleGet get ->
                    walkAll(some(get.tuple()), reads, bound, absorbed, reach, found, contexts);
            case Core.OptionSome option ->
                    walkAll(some(option.value()), reads, bound, absorbed, reach, found, contexts);
            case Core.Binary binary -> walkAll(some(binary.left(), binary.right()), reads, bound,
                    absorbed, reach, found, contexts);
            case Core.Call call ->
                    walkAll(call.args(), reads, bound, absorbed, reach, found, contexts);
            case Core.PreservedCall call ->
                    walkAll(call.args(), reads, bound, absorbed, reach, found, contexts);
            case Core.Apply apply ->
                    walkAll(apply.args(), reads, bound, absorbed, reach, found, contexts);
            case Core.ListLit list ->
                    walkAll(list.elements(), reads, bound, absorbed, reach, found, contexts);
            case Core.Tuple tuple ->
                    walkAll(tuple.elements(), reads, bound, absorbed, reach, found, contexts);
            case Core.Construct construct -> walkAll(
                    construct.values().stream().map(Core.FieldValue::value).toList(),
                    reads, bound, absorbed, reach, found, contexts);
        }
    }

    private void walkAll(List<Core> parts, InputReads reads, Map<BindingId, List<Arrival>> bound,
                         Set<Core> absorbed, List<Decision> reach, List<Interaction> found,
                         int contexts) {
        for (Core each : parts) {
            walk(each, reads, bound, absorbed, reach, found, contexts);
        }
    }

    /**
     * The path contexts arm {@code part} is read under, each held to what already held above it.
     *
     * <p>Empty where no row reaches the arm at all, which is a different answer from the one way in
     * this falls back to where the condition's ways cannot be enumerated — and a different answer
     * again from the arm having no way in that can be named, which is also empty and is where the
     * walk stops for the reason it always did.
     */
    private List<List<Decision>> waysInTo(Core.If iff, int part, InputReads reads,
                                          Map<BindingId, List<Arrival>> bound,
                                          List<Decision> reach, int contexts) {
        List<List<Decision>> ways = compatible(reach, waysInFor(iff, part, reads, bound));
        if (contexts * ways.size() <= MOST_WAYS_IN) {
            return ways;
        }
        // Over the bound, and read the one way it was read before the ways in were told apart. The
        // fallback is never itself over the bound: it is one way in, and what is already spent is
        // held under the bound by this same test.
        return compatible(reach, fallbackWayIn(iff, part, reads));
    }

    /**
     * The ways the condition comes out for arm {@code part}, or the arm itself where it cannot say.
     *
     * <p>The reach is no part of this. What the condition can come out as is a fact about the
     * condition, and holding it to what already held is the caller's, which the outcomes of a value
     * and the walk into an arm do differently.
     */
    private List<List<Decision>> waysInFor(Core.If iff, int part, InputReads reads,
                                           Map<BindingId, List<Arrival>> bound) {
        if (waysTo(iff.cond(), part == 0, reads, bound) instanceof Ways.Known known) {
            return known.paths();
        }
        return fallbackWayIn(iff, part, reads);
    }

    /** The arm itself as the one way in, for a condition this reading cannot value. */
    private List<List<Decision>> fallbackWayIn(Core.If iff, int part, InputReads reads) {
        Decision back = armFallback(iff, part, reads);
        return back == null ? List.of() : List.of(List.of(back));
    }

    /** Each way in held to what already held, leaving out the ones that contradict it. */
    private static List<List<Decision>> compatible(List<Decision> reach,
                                                   List<List<Decision>> ways) {
        List<List<Decision>> out = new ArrayList<>();
        for (List<Decision> way : ways) {
            List<Decision> merged = merge(reach, way);
            if (merged != null) {
                out.add(merged);
            }
        }
        return out;
    }

    /**
     * Both sets of conditions, or null where between them they settle one decision two ways.
     *
     * <p>One rule for every place two of these are put together: the parts of a value, a way in
     * held to the way in above it, the left of an operator that stops early held to what runs after
     * it. A decision read twice is one decision, and one settled two ways is no path.
     */
    private static List<Decision> merge(List<Decision> holds, List<Decision> more) {
        List<Decision> both = new ArrayList<>(holds);
        for (Decision each : more) {
            if (both.contains(each)) {
                continue;
            }
            if (disagrees(both, each)) {
                return null;
            }
            both.add(each);
        }
        return both;
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
            case Core.Binary binary when shortCircuits(binary.op()) -> null;
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

    /**
     * Whether the operator settles its answer without evaluating both sides.
     *
     * <p>{@code &&} stops at a left that is false and {@code ||} at a left that is true, so the two
     * sides are not consumed into one value and a product of them would ask for the combinations
     * the short circuit never reaches. Not a meeting, and it has paths to a value all the same:
     * the left settling the answer on its own, and the left going through with the right settling
     * it. Which of the left's paths go through is which value each comes to, which is why the
     * reading answers that as well as the conditions.
     */
    private static boolean shortCircuits(Hir.BinOp op) {
        return op == Hir.BinOp.AND || op == Hir.BinOp.OR;
    }

    /** Whether the operator answers with which way two values came out against each other. */
    private static boolean compares(Hir.BinOp op) {
        return switch (op) {
            case EQ, NE, LT, LE, GT, GE -> true;
            case AND, OR, ADD, SUB, MUL, DIV, CONCAT -> false;
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

    /** What a value nothing forks is settled by, which is the same thing however it is written. */
    private static List<Arrival> oneWay() {
        return List.of(new Arrival(new Outcome(List.of()), Truth.UNKNOWN));
    }

    /**
     * Whether {@code e} is a path to a value, which is what an outcome has to be.
     *
     * <p>The invariant the whole reading turns on. An outcome is a way the operand <em>arrives at a
     * value</em>, and a branch of the syntax is not that on its own: an arm answering
     * {@code unreachable} answers nothing and aborts, so counting it as a way the operand is settled
     * says the value varies where it does not — and the group it makes asks for rows at a
     * combination the body has no path to, which is the defect this reading exists to remove.
     *
     * <p>{@link NormalReturn} is the reading that owns the question and the one the arms of a body
     * are already told apart by. Answered here for the node the walk is at and for each arm it
     * enumerates, which are the two places a branch could be taken for a path.
     *
     * <p>Kept because it is asked at every node and answers about the whole subtree under it.
     */
    private boolean answers(Core e) {
        if (e == null) {
            return false;
        }
        Boolean already = reaches.get(e);
        if (already != null) {
            return already;
        }
        boolean answer = NormalReturn.of(e);
        reaches.put(e, answer);
        return answer;
    }

    /**
     * The ways {@code e} can be settled, as the conditions that hold when it is.
     *
     * <p>A projection of {@link #arrivalsOf} and not a second reading of the tree. What a value
     * comes to is asked of the same walk that asks under what conditions, because two walks over
     * one tree are two answers that have to agree and one place for them to stop agreeing.
     */
    private List<Outcome> outcomesOf(Core e, InputReads reads,
                                     Map<BindingId, List<Arrival>> bound) {
        return arrivalsOf(e, reads, bound).stream().map(Arrival::by).toList();
    }

    /**
     * The paths {@code e} arrives at a value by, each saying what it comes to where that is known.
     *
     * <p>Four shapes are read off the node and the rest is one rule rather than a case each: a
     * value built out of several is settled every way its parts are settled together, which is
     * their product. That is a rule about every other node and not an arm nobody filled in — what
     * it does not cover is exactly what forks, what stops early, what names, and what comes out one
     * of two ways against another value.
     */
    private List<Arrival> arrivalsOf(Core e, InputReads reads,
                                     Map<BindingId, List<Arrival>> bound) {
        if (e == null) {
            return oneWay();
        }
        List<Arrival> already = settled.get(e);
        if (already != null) {
            return already;
        }
        List<Arrival> answer = reading(e, reads, bound);
        settled.put(e, answer);
        return answer;
    }

    private List<Arrival> reading(Core e, InputReads reads, Map<BindingId, List<Arrival>> bound) {
        if (!answers(e)) {
            // Nothing arrives at a value here, so there is no way this is settled to enumerate.
            return oneWay();
        }
        if (e instanceof Core.Bool literal) {
            // One path, and the reading knows where it goes. Nothing about the inputs is on it.
            return List.of(new Arrival(new Outcome(List.of()),
                    literal.value() ? Truth.TRUE : Truth.FALSE));
        }
        if (e instanceof Core.Binary binary && shortCircuits(binary.op())) {
            return through(binary, reads, bound);
        }
        if (e instanceof Core.Match match) {
            TermPath at = reads.pathOf(match.scrutinee(), symbols);
            List<Arrival> out = new ArrayList<>();
            for (int part = 0; part < match.cases().size(); part++) {
                Core.Case each = match.cases().get(part);
                if (!answers(each.body())) {
                    continue;
                }
                Decision when = caseCondition(at, each, match, part);
                if (when == null) {
                    continue;
                }
                under(List.of(when), arrivalsOf(each.body(), reads, bound), out);
                if (out.size() > MOST_OUTCOMES) {
                    return oneWay();
                }
            }
            return out.isEmpty() ? oneWay() : out;
        }
        if (e instanceof Core.If iff) {
            // Numbered where they are written and not where they survive: the arm a fork answers on
            // is its place among the arms, and one that answers nothing is skipped rather than
            // closing the gap and letting the next arm be called the first.
            Core[] arms = {iff.then(), iff.els()};
            List<Arrival> out = new ArrayList<>();
            for (int part = 0; part < arms.length; part++) {
                if (!answers(arms[part])) {
                    continue;
                }
                // One way in per way the condition comes out that way, and the arm is settled every
                // way it is settled under each of them. Held under the outcome bound and not the
                // one on the ways in: this is a product taken at one node, which is what that bound
                // is about.
                for (List<Decision> way : waysInFor(iff, part, reads, bound)) {
                    under(way, arrivalsOf(arms[part], reads, bound), out);
                }
                if (out.size() > MOST_OUTCOMES) {
                    return oneWay();
                }
            }
            return out.isEmpty() ? oneWay() : out;
        }
        if (e instanceof Core.IfConstructed constructed) {
            // A fork, and not a value made of its arms — a product over them would say it is
            // settled every way they are together. Which arm is taken is whether the values made
            // the thing, which no position of the input names, so the ways it comes out are said
            // of the fork and a group over them is not offered.
            List<Core> arms = new ArrayList<>();
            arms.add(constructed.then());
            constructed.els().forEach(each -> arms.add(each.body()));
            List<Arrival> out = new ArrayList<>();
            for (int part = 0; part < arms.size(); part++) {
                if (!answers(arms.get(part))) {
                    continue;
                }
                Decision when = forkDecision(constructed, part);
                if (when == null) {
                    continue;
                }
                under(List.of(when), arrivalsOf(arms.get(part), reads, bound), out);
                if (out.size() > MOST_OUTCOMES) {
                    return oneWay();
                }
            }
            return out.isEmpty() ? oneWay() : out;
        }
        if (e instanceof Core.Read read) {
            List<Arrival> named = bound.get(read.binding());
            return named != null ? named : oneWay();
        }
        if (e instanceof Core.LetIn let) {
            Map<BindingId, List<Arrival>> inner = new HashMap<>(bound);
            inner.put(let.binder().binding(), arrivalsOf(let.value(), reads, bound));
            return arrivalsOf(let.body(), reads.and(let.binder(), let.value()), inner);
        }
        List<Arrival> out = oneWay();
        for (Core child : childrenOf(e)) {
            out = product(out, arrivalsOf(child, reads, bound));
            if (out.size() > MOST_OUTCOMES) {
                return oneWay();
            }
        }
        // A comparison whose two ways can both be named is a value this reading knows the truth of,
        // said of the position the comparison is about because that is what a row is steered by.
        //
        // Both ways or neither. With one of them the other's absence reads as a truth the value
        // never comes to, and a fork on it would be told one of its arms is never reached.
        //
        // Asked where nothing under the comparison was already saying the value varies, so that
        // what is read here is added to the reading and nothing is taken out of it: under
        // {@code a > f(b)} the fold has the ways {@code f(b)} is settled, and they are about
        // positions this would say nothing about.
        if (out.size() == 1 && e instanceof Core.Binary comparison && compares(comparison.op())) {
            Decision held = sideDecision(comparison, true, reads);
            Decision failed = sideDecision(comparison, false, reads);
            if (held != null && failed != null) {
                List<Decision> under = out.get(0).by().holds();
                List<Decision> whenHeld = merge(under, List.of(held));
                List<Decision> whenFailed = merge(under, List.of(failed));
                if (whenHeld != null && whenFailed != null) {
                    return List.of(new Arrival(new Outcome(whenHeld), Truth.TRUE),
                            new Arrival(new Outcome(whenFailed), Truth.FALSE));
                }
            }
        }
        return out;
    }

    /**
     * The paths to the value of an operator that stops as soon as its answer is settled.
     *
     * <p>Not a product of the two sides. {@code &&} comes to false wherever the left does and never
     * looks at the right, and comes to whatever the right does wherever the left went through — so
     * the paths are the left's settling ones as they stand, and the left's going-through ones each
     * extended by every path of the right.
     *
     * <p>A left path this reading cannot value stops where a settling one stops. Whether the right
     * ran at all is what the left's value would have said, so nothing is known about what comes
     * after it and the path is left saying what it already says.
     */
    private List<Arrival> through(Core.Binary binary, InputReads reads,
                                  Map<BindingId, List<Arrival>> bound) {
        Truth goesOn = binary.op() == Hir.BinOp.AND ? Truth.TRUE : Truth.FALSE;
        List<Arrival> out = new ArrayList<>();
        for (Arrival left : arrivalsOf(binary.left(), reads, bound)) {
            if (left.knownTruth() != goesOn) {
                out.add(left);
                continue;
            }
            under(left.by().holds(), arrivalsOf(binary.right(), reads, bound), out);
            if (out.size() > MOST_OUTCOMES) {
                return oneWay();
            }
        }
        return out.isEmpty() ? oneWay() : out;
    }

    /** Each arrival held to what already holds along the way to it, into {@code out}. */
    private static void under(List<Decision> holds, List<Arrival> arrivals, List<Arrival> out) {
        for (Arrival each : arrivals) {
            List<Decision> both = merge(holds, each.by().holds());
            if (both != null) {
                out.add(new Arrival(new Outcome(both), each.knownTruth()));
            }
        }
    }

    /**
     * The ways {@code e} is settled to {@code want}, or that this reading cannot enumerate them.
     *
     * <p>All of them or none. One arrival whose truth is unread is a path that may be among the
     * ways to either truth, so no list of them is complete while it is there — and an incomplete
     * list is worse here than no list, because whatever takes one reads the paths it does not hold
     * as paths the body has not got.
     */
    private Ways waysTo(Core e, boolean want, InputReads reads,
                        Map<BindingId, List<Arrival>> bound) {
        List<List<Decision>> paths = new ArrayList<>();
        for (Arrival each : arrivalsOf(e, reads, bound)) {
            if (each.knownTruth() == Truth.UNKNOWN) {
                return new Ways.Unknown();
            }
            if ((each.knownTruth() == Truth.TRUE) == want) {
                paths.add(each.by().holds());
            }
        }
        return new Ways.Known(paths);
    }

    /** Which case of the union this arm is, said of the position matched on where there is one, or
     *  null where no run through the arm could be recorded. */
    private Decision caseCondition(TermPath at, Core.Case arm, Core.Match match, int part) {
        souther.compiler.coverage.ControlClaim claim = armClaim(match, part);
        if (claim == null) {
            return null;
        }
        if (at == null) {
            Condition fork = forkArm(match, part);
            return fork == null ? null : new Decision(fork, claim);
        }
        List<String> names = arm.pattern().selectors().stream()
                .map(selector -> selector.name().name()).toList();
        return new Decision(new Condition.Case(at, String.join("|", names)), claim);
    }

    /**
     * That a run went down arm {@code part}, where nothing said which comparison sent it there.
     *
     * <p>What the walk falls back on. Where the condition's ways can be enumerated they are what
     * names the way in, on the comparisons a row is steered by; this is the answer for a condition
     * whose value this reading cannot say, and it is the answer every fork used to get.
     *
     * <p>An arm places at no class of any input, so a group offered under one of these goes. That
     * it is here at all is what says the reading found a way in it could not name.
     */
    private Decision armFallback(Core.If iff, int part, InputReads reads) {
        souther.compiler.coverage.ControlClaim claim = armClaim(iff, part);
        if (claim == null) {
            return null;
        }
        TermPath read = reads.pathOf(iff.cond(), symbols);
        Condition what = read == null ? forkArm(iff, part)
                : new Condition.Case(read, part == 0 ? "true" : "false");
        return what == null ? null : new Decision(what, claim);
    }

    /**
     * That {@code comparison} came out {@code held}, said of the position it is about, or null
     * where this reading cannot say which position that is or where no run could be shown to have
     * reached it.
     *
     * <p>The comparison and not the arm. A condition stops as soon as it is settled, so under
     * {@code A && B} the arm taken when the condition fails is reached both by a value that made
     * {@code B} false and by one that never evaluated {@code B}: a row is steered by getting the
     * comparison to answer, which no arm records.
     */
    private Decision sideDecision(Core.Binary comparison, boolean held, InputReads reads) {
        souther.compiler.coverage.ComparisonOccurrence site =
                plan.comparisonAt(comparison).orElse(null);
        TermPath at = firstOf(reads.pathOf(comparison.left(), symbols),
                reads.pathOf(comparison.right(), symbols));
        if (site == null || at == null) {
            return null;
        }
        return plan.outcomeOf(comparison, held)
                .flatMap(souther.compiler.coverage.ControlClaim::of)
                .map(claim -> new Decision(new Condition.Side(at, site, held), claim))
                .orElse(null);
    }

    /** One arm of a fork, where a run through it can be recorded, and null where it cannot. */
    private souther.compiler.coverage.ControlClaim armClaim(Core fork, int part) {
        ControlPointId.ArmOccurrence[] arms = plan.armsOf(fork);
        if (arms == null || part >= arms.length) {
            return null;
        }
        return souther.compiler.coverage.ControlClaim.of(arms[part]).orElse(null);
    }

    /** The fork itself, for a decision this reading cannot name a position for, or null where the
     *  plan named no fork here. */
    private Condition forkArm(Core fork, int part) {
        souther.compiler.coverage.ForkOccurrence named = plan.forkAt(fork);
        return named == null ? null : new Condition.Arm(named, part);
    }

    /** A fork coming out one way and nothing said about which position, or null where no run
     *  through the arm could be recorded. */
    private Decision forkDecision(Core fork, int part) {
        souther.compiler.coverage.ControlClaim claim = armClaim(fork, part);
        Condition what = forkArm(fork, part);
        return claim == null || what == null ? null : new Decision(what, claim);
    }

    private static TermPath firstOf(TermPath left, TermPath right) {
        return left != null ? left : right;
    }

    /**
     * Every way the two can be settled together, which is not every pairing of them.
     *
     * <p>A binding read twice is one decision read twice, and pairing its outcomes without asking
     * whether the two agree would report a value settled nine ways that is settled three.
     *
     * <p>What the parts of a value come to is not what the value comes to. A thing built out of
     * several is the constructor's answer and no path of it carries a truth of its own, so these
     * arrive with nothing said about which of the two they are — which is what a comparison over
     * the whole of it goes on to say, where it can.
     */
    private static List<Arrival> product(List<Arrival> left, List<Arrival> right) {
        List<Arrival> out = new ArrayList<>();
        for (Arrival one : left) {
            for (Arrival other : right) {
                List<Decision> holds = merge(one.by().holds(), other.by().holds());
                if (holds != null) {
                    out.add(new Arrival(new Outcome(holds), Truth.UNKNOWN));
                }
                if (out.size() > MOST_OUTCOMES) {
                    return out;
                }
            }
        }
        return out;
    }

    /**
     * Whether {@code added} settles a decision the conditions already settle the other way.
     *
     * <p>The same decision and a different way out of it, which is two things and not one. A
     * decision named twice and settled the same way is one run doing one thing twice over —
     * {@code if a then (if a then …)} is written as two forks and no row takes one of them without
     * the other — and reading that as a contradiction would take away a path the body has.
     *
     * <p>Which decision it is is not which place a run is recorded at. Two forks on one flag are
     * two places and one decision, so what is compared is what the condition is about and never the
     * claim beside it.
     */
    private static boolean disagrees(List<Decision> holds, Decision added) {
        for (Decision already : holds) {
            Condition each = already.constrains();
            boolean otherWay = switch (added.constrains()) {
                case Condition.Case one -> each instanceof Condition.Case other
                        && other.at().equals(one.at()) && !other.name().equals(one.name());
                case Condition.Side one -> each instanceof Condition.Side other
                        && other.comparison().equals(one.comparison()) && other.held() != one.held();
                case Condition.Arm one -> each instanceof Condition.Arm other
                        && other.fork().equals(one.fork()) && other.part() != one.part();
            };
            if (otherWay) {
                return true;
            }
        }
        return false;
    }

    /** Every value this node is built out of, in the order it is written. */
    private static List<Core> childrenOf(Core node) {
        return switch (node) {
            case Core.Int ignored -> List.of();
            case Core.Decimal ignored -> List.of();
            case Core.Str ignored -> List.of();
            case Core.Bool ignored -> List.of();
            case Core.Temporal ignored -> List.of();
            case Core.Read ignored -> List.of();
            case Core.UnitValue ignored -> List.of();
            case Core.OptionNone ignored -> List.of();
            case Core.Unreachable ignored -> List.of();
            case Core.Neg neg -> some(neg.operand());
            case Core.FieldAccess access -> some(access.target());
            case Core.TupleGet get -> some(get.tuple());
            case Core.OptionSome option -> some(option.value());
            case Core.Binary binary -> some(binary.left(), binary.right());
            case Core.Call call -> call.args();
            case Core.PreservedCall call -> call.args();
            case Core.Apply apply -> apply.args();
            case Core.ListLit list -> list.elements();
            case Core.Tuple tuple -> tuple.elements();
            case Core.Construct construct ->
                    construct.values().stream().map(Core.FieldValue::value).toList();
            case Core.If iff -> some(iff.cond(), iff.then(), iff.els());
            case Core.LetIn let -> some(let.value(), let.body());
            // Not the body. Evaluating this makes the function, and what the body comes to when
            // something calls it is that call's business — the same stance the reading of whether a
            // value arrives takes, and for the same reason.
            case Core.Block ignored -> List.of();
            case Core.Match match -> {
                List<Core> out = new ArrayList<>();
                out.add(match.scrutinee());
                match.cases().forEach(each -> out.add(each.body()));
                yield out;
            }
            case Core.IfConstructed constructed -> {
                List<Core> out = new ArrayList<>();
                out.add(constructed.construct());
                out.add(constructed.then());
                constructed.els().forEach(arm -> out.add(arm.body()));
                yield out;
            }
        };
    }
}
