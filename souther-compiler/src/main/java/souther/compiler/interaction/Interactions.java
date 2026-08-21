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
 * <p>Under-reading is the safe direction. A group nothing formed is an obligation nobody is asked
 * for, which is where a product over the input positions already leaves things; a group formed too
 * eagerly asks for rows that establish nothing. Both limits below take that direction: a value that
 * can be settled more ways than the reading will tell apart is answered as settled one way.
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

    private final CoverageSites.Plan plan;
    private final Symbols symbols;

    /**
     * What each node was settled by, so an enclosing meeting does not fold over it again.
     *
     * <p>Keyed by identity and sound because a node occurs once: what is in scope at it is what the
     * walk had when it got there, so the environments are a function of the position and not a
     * second key.
     */
    private final IdentityHashMap<Core, List<Outcome>> settled = new IdentityHashMap<>();

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
                java.util.Collections.newSetFromMap(new IdentityHashMap<>()), List.of(), found);
        return List.copyOf(found);
    }

    private void walk(Core node, InputReads reads, Map<BindingId, List<Outcome>> bound,
                      Set<Core> absorbed, List<Decision> reach, List<Interaction> found) {
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
            walk(let.value(), reads, bound, absorbed, reach, found);
            Map<BindingId, List<Outcome>> inner = new HashMap<>(bound);
            inner.put(let.binder().binding(), outcomesOf(let.value(), reads, bound));
            walk(let.body(), reads.and(let.binder(), let.value()), inner, absorbed, reach, found);
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
        descend(node, reads, bound, absorbed, reach, found);
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
    private void descend(Core node, InputReads reads, Map<BindingId, List<Outcome>> bound,
                         Set<Core> absorbed, List<Decision> reach, List<Interaction> found) {
        switch (node) {
            // A way in nobody can name stops the walk into that arm, whether what could not be named
            // is the position the decision is about or the place a run that took it would be seen at.
            // A group found in there would be under a condition nothing can steer a row into or hold
            // a run to, and offering it asks for a row that may never arrive.
            case Core.If iff -> {
                walk(iff.cond(), reads, bound, absorbed, reach, found);
                Core[] arms = {iff.then(), iff.els()};
                for (int part = 0; part < arms.length; part++) {
                    Decision went = armCondition(iff, part, reads);
                    if (went != null) {
                        walk(arms[part], reads, bound, absorbed, and(reach, went), found);
                    }
                }
            }
            case Core.Match match -> {
                TermPath at = reads.pathOf(match.scrutinee(), symbols);
                walk(match.scrutinee(), reads, bound, absorbed, reach, found);
                for (int part = 0; part < match.cases().size(); part++) {
                    Core.Case each = match.cases().get(part);
                    Decision went = caseCondition(at, each, match, part);
                    if (went != null) {
                        walk(each.body(), reads, bound, absorbed, and(reach, went), found);
                    }
                }
            }
            case Core.Binary binary when shortCircuits(binary.op()) -> {
                walk(binary.left(), reads, bound, absorbed, reach, found);
                // The right runs only where the left did not settle the answer, and which of the
                // left's outcomes that is takes reading a value rather than a condition. Where the
                // left is one this can say a side of, that side is what getting here takes; where
                // it is not, there is nothing to say and the walk does not go in.
                Decision went = settledBy(binary.left(), binary.op() == Hir.BinOp.AND, reads);
                if (went != null) {
                    walk(binary.right(), reads, bound, absorbed, and(reach, went), found);
                }
            }
            case Core.IfConstructed constructed -> {
                // The values are made, and which arm is taken is whether making the thing out of
                // them held its rules. No class of an input names that, so what is inside the arms
                // is not walked: a row cannot be steered to either of them, and one offered for a
                // group in there would be offered for a combination it may not sit in.
                for (Core.FieldValue given : constructed.construct().values()) {
                    walk(given.value(), reads, bound, absorbed, reach, found);
                }
            }
            case Core.Block ignored -> {
                // Evaluating this makes the function; the body runs where something calls it, under
                // whatever it is called with. That is not a condition on the inputs of this
                // behavior, so a group in there has no way in this can name.
            }
            case Core.LetIn let -> {
                walk(let.value(), reads, bound, absorbed, reach, found);
                walk(let.body(), reads.and(let.binder(), let.value()), bound, absorbed, reach,
                        found);
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
            case Core.Neg neg -> walkAll(some(neg.operand()), reads, bound, absorbed, reach, found);
            case Core.FieldAccess access ->
                    walkAll(some(access.target()), reads, bound, absorbed, reach, found);
            case Core.TupleGet get -> walkAll(some(get.tuple()), reads, bound, absorbed, reach, found);
            case Core.OptionSome option ->
                    walkAll(some(option.value()), reads, bound, absorbed, reach, found);
            case Core.Binary binary ->
                    walkAll(some(binary.left(), binary.right()), reads, bound, absorbed, reach, found);
            case Core.Call call -> walkAll(call.args(), reads, bound, absorbed, reach, found);
            case Core.PreservedCall call ->
                    walkAll(call.args(), reads, bound, absorbed, reach, found);
            case Core.Apply apply -> walkAll(apply.args(), reads, bound, absorbed, reach, found);
            case Core.ListLit list -> walkAll(list.elements(), reads, bound, absorbed, reach, found);
            case Core.Tuple tuple -> walkAll(tuple.elements(), reads, bound, absorbed, reach, found);
            case Core.Construct construct -> walkAll(
                    construct.values().stream().map(Core.FieldValue::value).toList(),
                    reads, bound, absorbed, reach, found);
        }
    }

    private void walkAll(List<Core> parts, InputReads reads, Map<BindingId, List<Outcome>> bound,
                         Set<Core> absorbed, List<Decision> reach, List<Interaction> found) {
        for (Core each : parts) {
            walk(each, reads, bound, absorbed, reach, found);
        }
    }

    /** The way in, and one more thing that holds along it. */
    private static List<Decision> and(List<Decision> reach, Decision went) {
        List<Decision> both = new ArrayList<>(reach);
        both.add(went);
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
     * sides are not consumed into one value: the paths to a value are the left settling the answer
     * on its own, and the left going through with the right settling it. Which of the left's
     * outcomes settles it is which value it comes to, and this reading has conditions rather than
     * values — so the answer is that the operator is settled one way, which asks for nothing. A
     * product of the two sides would ask for the combinations the short circuit never reaches.
     */
    private static boolean shortCircuits(Hir.BinOp op) {
        return op == Hir.BinOp.AND || op == Hir.BinOp.OR;
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
    private static List<Outcome> oneWay() {
        return List.of(new Outcome(List.of()));
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
     * <p>Three shapes are read off the node and the rest is one rule rather than a case each: a
     * value built out of several is settled every way its parts are settled together, which is
     * their product. That is a rule about every other node and not an arm nobody filled in — what
     * it does not cover is exactly what forks and what names.
     */
    private List<Outcome> outcomesOf(Core e, InputReads reads, Map<BindingId, List<Outcome>> bound) {
        if (e == null) {
            return oneWay();
        }
        List<Outcome> already = settled.get(e);
        if (already != null) {
            return already;
        }
        List<Outcome> answer = reading(e, reads, bound);
        settled.put(e, answer);
        return answer;
    }

    private List<Outcome> reading(Core e, InputReads reads, Map<BindingId, List<Outcome>> bound) {
        if (!answers(e)) {
            // Nothing arrives at a value here, so there is no way this is settled to enumerate.
            return oneWay();
        }
        if (e instanceof Core.Binary binary && shortCircuits(binary.op())) {
            return oneWay();
        }
        if (e instanceof Core.Match match) {
            TermPath at = reads.pathOf(match.scrutinee(), symbols);
            List<Outcome> out = new ArrayList<>();
            for (int part = 0; part < match.cases().size(); part++) {
                Core.Case each = match.cases().get(part);
                if (!answers(each.body())) {
                    continue;
                }
                Decision when = caseCondition(at, each, match, part);
                if (when == null) {
                    continue;
                }
                for (Outcome inner : outcomesOf(each.body(), reads, bound)) {
                    out.add(prepend(when, inner));
                }
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
            List<Outcome> out = new ArrayList<>();
            for (int part = 0; part < arms.length; part++) {
                if (!answers(arms[part])) {
                    continue;
                }
                Decision when = armCondition(iff, part, reads);
                if (when == null) {
                    continue;
                }
                for (Outcome inner : outcomesOf(arms[part], reads, bound)) {
                    out.add(prepend(when, inner));
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
            List<Outcome> out = new ArrayList<>();
            for (int part = 0; part < arms.size(); part++) {
                if (!answers(arms.get(part))) {
                    continue;
                }
                Decision when = forkDecision(constructed, part);
                if (when == null) {
                    continue;
                }
                for (Outcome inner : outcomesOf(arms.get(part), reads, bound)) {
                    out.add(prepend(when, inner));
                }
                if (out.size() > MOST_OUTCOMES) {
                    return oneWay();
                }
            }
            return out.isEmpty() ? oneWay() : out;
        }
        if (e instanceof Core.Read read) {
            List<Outcome> named = bound.get(read.binding());
            return named != null ? named : oneWay();
        }
        if (e instanceof Core.LetIn let) {
            Map<BindingId, List<Outcome>> inner = new HashMap<>(bound);
            inner.put(let.binder().binding(), outcomesOf(let.value(), reads, bound));
            return outcomesOf(let.body(), reads.and(let.binder(), let.value()), inner);
        }
        List<Outcome> out = oneWay();
        for (Core child : childrenOf(e)) {
            out = product(out, outcomesOf(child, reads, bound));
            if (out.size() > MOST_OUTCOMES) {
                return oneWay();
            }
        }
        return out;
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
     * Which way the fork came out, said of the comparison where the plan numbered one.
     *
     * <p>The comparison and not the arm, where there is one. A condition stops as soon as it is
     * settled, so under {@code A && B} the arm taken when the condition fails is reached both by a
     * value that made {@code B} false and by one that never evaluated {@code B}: a row is steered
     * by getting the comparison to answer, which no arm records.
     */
    private Decision armCondition(Core.If iff, int part, InputReads reads) {
        Decision said = settledBy(iff.cond(), part == 0, reads);
        if (said != null) {
            return said;
        }
        // The condition is a value rather than a comparison, so nothing recorded the way it came
        // out — what a run that went this way is seen to have done is that it took this arm.
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
     * That {@code test} came out {@code held}, said of the position it is about, or null where this
     * reading cannot say which position that is.
     *
     * <p>Asked of a fork's condition and of the left of an operator that stops early, which are the
     * same question: both are a value whose coming out one way is what a row has to arrange.
     */
    private Decision settledBy(Core test, boolean held, InputReads reads) {
        if (!(test instanceof Core.Binary comparison)) {
            // The condition is a value rather than a comparison, and nothing records a value coming
            // out one way. Whether the arm below says it is the caller's question: under a fork
            // there is an arm to be held to, and on the left of an operator that stops early there
            // is not.
            return null;
        }
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

    private static Outcome prepend(Decision when, Outcome outcome) {
        List<Decision> holds = new ArrayList<>();
        holds.add(when);
        holds.addAll(outcome.holds());
        return new Outcome(holds);
    }

    /**
     * Every way the two can be settled together, which is not every pairing of them.
     *
     * <p>A binding read twice is one decision read twice, and pairing its outcomes without asking
     * whether the two agree would report a value settled nine ways that is settled three.
     */
    private static List<Outcome> product(List<Outcome> left, List<Outcome> right) {
        List<Outcome> out = new ArrayList<>();
        for (Outcome one : left) {
            for (Outcome other : right) {
                List<Decision> holds = new ArrayList<>(one.holds());
                boolean agree = true;
                for (Decision each : other.holds()) {
                    if (holds.contains(each)) {
                        continue;
                    }
                    if (disagrees(holds, each)) {
                        agree = false;
                        break;
                    }
                    holds.add(each);
                }
                if (agree) {
                    out.add(new Outcome(holds));
                }
                if (out.size() > MOST_OUTCOMES) {
                    return out;
                }
            }
        }
        return out;
    }

    /** Whether {@code added} settles a decision the outcome already settles the other way. */
    private static boolean disagrees(List<Decision> holds, Decision added) {
        for (Decision already : holds) {
            Condition each = already.constrains();
            boolean same = switch (added.constrains()) {
                case Condition.Case one ->
                        each instanceof Condition.Case other && other.at().equals(one.at());
                case Condition.Side one -> each instanceof Condition.Side other
                        && other.comparison().equals(one.comparison());
                case Condition.Arm one -> each instanceof Condition.Arm other
                        && other.fork().equals(one.fork());
            };
            if (same) {
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
