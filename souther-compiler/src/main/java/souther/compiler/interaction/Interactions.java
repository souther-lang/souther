package souther.compiler.interaction;

import souther.compiler.core.Core;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;

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
 * <p>Under-reading is the safe direction. A group nothing formed is an obligation nobody is asked
 * for, which is where a product over the input positions already leaves things; a group formed too
 * eagerly asks for rows that establish nothing.
 */
public final class Interactions {

    private Interactions() {}

    /** The groups of {@code body}, in the order the walk meets them. */
    public static List<Interaction> of(String behavior, Core body, CoverageSites.Plan plan) {
        List<Interaction> found = new ArrayList<>();
        walk(body, plan, found);
        return List.copyOf(found);
    }

    private static void walk(Core node, CoverageSites.Plan plan, List<Interaction> found) {
        List<Core> meeting = meetingAt(node);
        if (meeting != null) {
            List<Factor> factors = new ArrayList<>();
            for (Core operand : meeting) {
                List<Outcome> outcomes = outcomesOf(operand, plan);
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
            walk(child, plan, found);
        }
    }

    /** The values consumed into one here, or null where this node consumes none. */
    private static List<Core> meetingAt(Core node) {
        return switch (node) {
            case Core.Binary binary -> List.of(binary.left(), binary.right());
            case Core.Call call -> call.args().size() > 1 ? call.args() : null;
            case Core.PreservedCall call -> call.args().size() > 1 ? call.args() : null;
            case Core.Apply apply -> apply.args().size() > 1 ? apply.args() : null;
            default -> null;
        };
    }

    /**
     * The ways {@code e} can be settled, as the conditions that hold when it is.
     *
     * <p>Two shapes are read off the node and the rest is one rule rather than a case each: a value
     * built out of several is settled every way its parts are settled together, which is their
     * product. That is a rule about every other node and not an arm nobody filled in — what it does
     * not cover is exactly what forks.
     */
    private static List<Outcome> outcomesOf(Core e, CoverageSites.Plan plan) {
        if (e instanceof Core.Match match) {
            TermPath at = pathOf(match.scrutinee());
            List<Outcome> out = new ArrayList<>();
            for (int part = 0; part < match.cases().size(); part++) {
                Core.Case each = match.cases().get(part);
                Condition when = caseCondition(at, each, match, part, plan);
                for (Outcome inner : outcomesOf(each.body(), plan)) {
                    out.add(prepend(when, inner));
                }
            }
            return out;
        }
        if (e instanceof Core.If iff) {
            List<Outcome> out = new ArrayList<>();
            List<Core> arms = List.of(iff.then(), iff.els());
            for (int part = 0; part < arms.size(); part++) {
                Condition when = armCondition(iff, part, plan);
                for (Outcome inner : outcomesOf(arms.get(part), plan)) {
                    out.add(prepend(when, inner));
                }
            }
            return out;
        }
        List<Outcome> out = List.of(new Outcome(List.of()));
        for (Core child : childrenOf(e)) {
            out = product(out, outcomesOf(child, plan));
        }
        return out;
    }

    /** Which case of the union this arm is, said of the position matched on where there is one. */
    private static Condition caseCondition(TermPath at, Core.Case arm, Core.Match match, int part,
                                           CoverageSites.Plan plan) {
        if (at == null) {
            return arm(match, part, plan);
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
    private static Condition armCondition(Core.If iff, int part, CoverageSites.Plan plan) {
        Integer site = plan.byComparison().get(iff.cond());
        TermPath at = iff.cond() instanceof Core.Binary comparison
                ? firstOf(pathOf(comparison.left()), pathOf(comparison.right())) : null;
        if (site == null || at == null) {
            return arm(iff, part, plan);
        }
        return new Condition.Side(at, site, part == 0);
    }

    /** The fork itself, for a decision this reading cannot name a position for. */
    private static Condition arm(Core fork, int part, CoverageSites.Plan plan) {
        ControlPointId.ArmOccurrence[] arms = plan.armsOf(fork);
        return new Condition.Arm(arms == null || arms.length == 0 ? -1 : arms[0].controlId(), part);
    }

    private static TermPath firstOf(TermPath left, TermPath right) {
        return left != null ? left : right;
    }

    /** Which input position {@code e} reads, or null where it is not one. */
    private static TermPath pathOf(Core e) {
        return switch (e) {
            case Core.Read read -> new TermPath(read.name(), List.of());
            case Core.FieldAccess access -> {
                TermPath base = pathOf(access.target());
                if (base == null) {
                    yield null;
                }
                List<String> fields = new ArrayList<>(base.fields());
                fields.add(access.field());
                yield new TermPath(base.head(), fields);
            }
            default -> null;
        };
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
            case Core.Neg neg -> List.of(neg.operand());
            case Core.FieldAccess access -> List.of(access.target());
            case Core.TupleGet get -> List.of(get.tuple());
            case Core.OptionSome some -> List.of(some.value());
            case Core.Binary binary -> List.of(binary.left(), binary.right());
            case Core.Call call -> call.args();
            case Core.PreservedCall call -> call.args();
            case Core.Apply apply -> apply.args();
            case Core.ListLit list -> list.elements();
            case Core.Tuple tuple -> tuple.elements();
            case Core.Construct construct ->
                    construct.values().stream().map(Core.FieldValue::value).toList();
            case Core.If iff -> List.of(iff.cond(), iff.then(), iff.els());
            case Core.LetIn let -> List.of(let.value(), let.body());
            case Core.Block block -> List.of(block.body());
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
