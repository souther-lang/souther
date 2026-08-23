package souther.compiler.core;

import souther.compiler.types.BinOp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * What an expression evaluates, in the order it evaluates them.
 *
 * <p>One account of evaluation order, for the readers that need one. Which reason an arm aborts
 * with and which fork a body reaches first are two questions about the same order, and each working
 * it out for itself is two chances to disagree about what runs before what.
 *
 * <p><b>Not a list, because not every part runs.</b> {@code &&} and {@code ||} stop as soon as the
 * answer is settled (spec §a-condition-stops-when-its-answer-is-settled): the right operand of
 * {@code x /= 0 && 100 / x > 1} runs on the runs where the left came out true and on no others. A
 * sequence cannot say that, and said as a sequence it is wrong in both directions at once — what the
 * right operand does is taken as done on every run, and what it aborts on is taken as aborting every
 * run. So a step says whether anything decides that it runs.
 *
 * <p>Which was here to be got wrong before anything read it. {@link Step.OnlyWhere} exists because
 * the walk that judges constructions now carries what one step leaves into the next, and a step it
 * takes as running on every run is one it stops the walk at.
 *
 * <p><b>Strict positions only, and exhaustive.</b> A branch, an arm, a binding's body and a
 * departure are not evaluated by reaching the node they are written in — reaching it evaluates what
 * decides which of them runs, and each of them is entered by whoever owns it under what choosing it
 * settles. So what comes back for such a node is the part that runs whenever the node does, and no
 * more. A node kind added to the IR stops here and is decided about rather than falling in with the
 * ones every part of which is evaluated.
 *
 * <p>Not {@link Core#forEachChild}, which hands over the slots of a node and is not an account of
 * evaluation. The two differ at a construction: the emitter walks the declared fields and picks
 * each one's initializer out, so what runs first is the field declared first and not the one
 * written first.
 *
 * <p>A {@code Block} is a function value: evaluating that position makes the function, and its body
 * runs when a call applies it, on arguments this position does not have.
 */
public final class Evaluated {

    /** One thing an expression evaluates, and what decides that it is evaluated. */
    public sealed interface Step {

        /** What runs. */
        Core expression();

        /** Evaluated whenever the expression it is a step of is. */
        record Always(Core expression) implements Step {}

        /**
         * Evaluated only on the runs where {@code asked} came out {@code comesOut} — which is what
         * a short-circuiting operator's right operand is, and the only thing that is one today.
         *
         * <p>The condition is carried rather than the operator, because what a reader needs is what
         * has to hold for this to run. Handed the operator instead, every reader would work the
         * polarity out again, and {@code ||} is the one they would get wrong.
         */
        record OnlyWhere(Core asked, boolean comesOut, Core expression) implements Step {}
    }

    /** The sub-expressions of {@code e} that run, in the order they run. */
    public static List<Step> inOrder(Core e) {
        return switch (e) {
            case Core.Int ignored -> List.of();
            case Core.Decimal ignored -> List.of();
            case Core.Str ignored -> List.of();
            case Core.Bool ignored -> List.of();
            case Core.Temporal ignored -> List.of();
            case Core.Read ignored -> List.of();
            case Core.UnitValue ignored -> List.of();
            case Core.OptionNone ignored -> List.of();
            // Answers nothing and aborts, and evaluates nothing on its way there.
            case Core.Unreachable ignored -> List.of();
            case Core.Neg neg -> always(neg.operand());
            case Core.FieldAccess access -> always(access.target());
            case Core.TupleGet get -> always(get.tuple());
            case Core.OptionSome option -> always(option.value());
            // The left, and then the right on the runs the left did not answer for. A false left
            // is the answer of a `&&` and a true left is the answer of an `||`, so what has to hold
            // for the right to run is the left coming out the other way.
            case Core.Binary binary when binary.op().stopsWhenItsAnswerIsSettled() ->
                    binary.left() == null || binary.right() == null
                            // A hole where an operand was. The left runs if it is there, and
                            // without a left to come out one way nothing decides the right — so it
                            // is not placed rather than placed wrongly. A body with a hole in it is
                            // one a clause was refused of, and every reading of it is already
                            // reading around what is missing.
                            ? always(binary.left())
                            : List.of(new Step.Always(binary.left()),
                                    new Step.OnlyWhere(binary.left(), binary.op() == BinOp.AND,
                                            binary.right()));
            case Core.Binary binary -> always(binary.left(), binary.right());
            // The callee's own body is not read; its arguments are evaluated before it is reached.
            case Core.Call call -> always(call.args());
            case Core.PreservedCall call -> always(call.args());
            // What is applied is a name holding a function, which is loaded and not run here.
            case Core.Apply apply -> always(apply.args());
            case Core.ListLit list -> always(list.elements());
            case Core.Tuple tuple -> always(tuple.elements());
            case Core.Construct construct ->
                    always(construct.values().stream().map(Core.FieldValue::value).toList());
            case Core.Block ignored -> List.of();
            // What decides which branch, which arm, or whether the value was built. The branches and
            // the arms are entered by whoever owns them, under what choosing one settles.
            case Core.If iff -> always(iff.cond());
            case Core.LetIn let -> always(let.value());
            case Core.Match match -> always(match.scrutinee());
            case Core.IfConstructed constructed -> always(constructed.construct());
        };
    }

    /**
     * The parts that are there, each a step that always runs.
     *
     * <p>A body the checker refused a clause of arrives with a hole where the clause was, and a
     * reading that is not the checker has nothing to say about it.
     */
    private static List<Step> always(Core... parts) {
        return always(Arrays.asList(parts));
    }

    private static List<Step> always(List<Core> parts) {
        List<Step> out = new ArrayList<>();
        for (Core each : parts) {
            if (each != null) {
                out.add(new Step.Always(each));
            }
        }
        return List.copyOf(out);
    }

    private Evaluated() {}
}
