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
                java.util.Collections.newSetFromMap(new IdentityHashMap<>()), found);
        return List.copyOf(found);
    }

    private void walk(Core node, InputReads reads, Map<BindingId, List<Outcome>> bound,
                      Set<Core> absorbed, List<Interaction> found) {
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
            // question.
            walk(let.value(), reads, bound, absorbed, found);
            Map<BindingId, List<Outcome>> inner = new HashMap<>(bound);
            inner.put(let.binder().binding(), outcomesOf(let.value(), reads, bound));
            walk(let.body(), reads.and(let.binder(), let.value()), inner, absorbed, found);
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
            if (factors.size() > 1) {
                found.add(new Interaction(factors));
            }
        }
        for (Core child : childrenOf(node)) {
            walk(child, reads, bound, absorbed, found);
        }
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
                Condition when = caseCondition(at, each, match, part);
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
                Condition when = armCondition(iff, part, reads);
                for (Outcome inner : outcomesOf(arms[part], reads, bound)) {
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

    /** Which case of the union this arm is, said of the position matched on where there is one. */
    private Condition caseCondition(TermPath at, Core.Case arm, Core.Match match, int part) {
        if (at == null) {
            return arm(match, part);
        }
        List<String> names = arm.pattern().selectors().stream()
                .map(selector -> selector.name().name()).toList();
        return new Condition.Case(at, String.join("|", names));
    }

    /**
     * Which way the fork came out, said of the comparison where the plan numbered one.
     *
     * <p>The comparison and not the arm, where there is one. A condition stops as soon as it is
     * settled, so under {@code A && B} the arm taken when the condition fails is reached both by a
     * value that made {@code B} false and by one that never evaluated {@code B}: a row is steered
     * by getting the comparison to answer, which no arm records.
     */
    private Condition armCondition(Core.If iff, int part, InputReads reads) {
        if (!(iff.cond() instanceof Core.Binary comparison)) {
            // The condition is the value. A Bool the body branches on is a position of its own and
            // the arms are its two classes, so the decision is said of it rather than of the fork.
            TermPath read = reads.pathOf(iff.cond(), symbols);
            return read == null ? arm(iff, part)
                    : new Condition.Case(read, part == 0 ? "true" : "false");
        }
        Integer site = plan.byComparison().get(comparison);
        TermPath at = firstOf(reads.pathOf(comparison.left(), symbols),
                reads.pathOf(comparison.right(), symbols));
        if (site == null || at == null) {
            return arm(iff, part);
        }
        return new Condition.Side(at, site, part == 0);
    }

    /** The fork itself, for a decision this reading cannot name a position for. */
    private Condition arm(Core fork, int part) {
        ControlPointId.ArmOccurrence[] arms = plan.armsOf(fork);
        return new Condition.Arm(arms == null || arms.length == 0 ? -1 : arms[0].controlId(), part);
    }

    private static TermPath firstOf(TermPath left, TermPath right) {
        return left != null ? left : right;
    }

    private static Outcome prepend(Condition when, Outcome outcome) {
        List<Condition> holds = new ArrayList<>();
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
                List<Condition> holds = new ArrayList<>(one.holds());
                boolean agree = true;
                for (Condition each : other.holds()) {
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
    private static boolean disagrees(List<Condition> holds, Condition added) {
        for (Condition each : holds) {
            boolean same = switch (added) {
                case Condition.Case one ->
                        each instanceof Condition.Case other && other.at().equals(one.at());
                case Condition.Side one ->
                        each instanceof Condition.Side other && other.site() == one.site();
                case Condition.Arm one ->
                        each instanceof Condition.Arm other && other.control() == one.control();
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
            case Core.Block block -> some(block.body());
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
