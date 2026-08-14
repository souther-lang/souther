package souther.compiler.coverage;

import souther.compiler.core.Core;

import java.util.List;

/**
 * Whether evaluating an expression can answer a value.
 *
 * <p>An {@code unreachable} answers none and aborts instead, and an expression that has to evaluate
 * one on its way answers none either. This is what tells an arm the rows can be in from an arm that
 * only states a combination the model rules out — the first is a fork a row takes, the second is not
 * an arm at all.
 *
 * <p>Read off the tree and not off the types. An {@code unreachable} is written as {@code Never}, but
 * the position it stands in usually states a shape, and that shape is what the elaborator records on
 * the node — so a {@code match} arm answering {@code unreachable} carries the type of what its
 * siblings answer. The node kind is what survives.
 *
 * <p>What a call answers is not looked into. A non-recursive helper is inlined into the body that uses
 * it, so its arms are already here; a recursive one is a shared method, and a helper that never
 * returns leaves the arm that calls it counted. The arguments are looked at, because they are
 * evaluated before the call is — but a function passed as one is made and not run, so what its body
 * does when the call gets round to it is the call's business and stays unread.
 */
public final class NormalReturn {

    /**
     * Whether {@code e} can be evaluated to a value.
     *
     * <p>Everything strict is required — an expression whose operand answers nothing answers nothing
     * — and a fork also needs one of the paths that leave it to answer something. Written as an
     * exhaustive switch: a node kind added to the IR should stop here and be decided about rather
     * than fall into a default and be assumed to answer.
     */
    public static boolean of(Core e) {
        return switch (e) {
            case Core.Unreachable _ -> false;
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Read _,
                 Core.UnitValue _, Core.OptionNone _ -> true;
            case Core.Neg n -> of(n.operand());
            case Core.FieldAccess fa -> of(fa.target());
            case Core.Binary b -> of(b.left()) && of(b.right());
            case Core.OptionSome s -> of(s.value());
            case Core.TupleGet tg -> of(tg.tuple());
            case Core.Tuple t -> all(t.elements());
            case Core.ListLit lit -> all(lit.elements());
            case Core.Construct nd -> nd.values().stream().allMatch(given -> of(given.value()));
            // The callee's own body is not read; its arguments are evaluated before it is reached.
            case Core.Call c -> all(c.args());
            case Core.Apply a -> all(a.args());
            case Core.PreservedCall p -> throw p.unexpectedIn("normal-return analysis");
            // The value is evaluated before the body it binds is.
            case Core.LetIn li -> of(li.value()) && of(li.body());
            // A function value, not a body being run here: a block is a step handed to a combinator
            // or a lambda a `let` binds, and evaluating this position makes the function rather than
            // calling it. What happens when it is called is the call's business, and a call is not
            // read through. Reading the body here says a step that aborts on an element it is never
            // handed makes the expression around it answer nothing — which would take a class a row
            // does sit in out of the denominator.
            case Core.Block _ -> true;
            case Core.If iff -> of(iff.cond()) && (of(iff.then()) || of(iff.els()));
            case Core.Match m -> of(m.scrutinee())
                    && m.cases().stream().anyMatch(arm -> of(arm.body()));
            case Core.IfConstructed ic ->
                    ic.construct().values().stream().allMatch(given -> of(given.value()))
                            && (of(ic.then()) || ic.els().stream().anyMatch(arm -> of(arm.body())));
        };
    }

    private static boolean all(List<Core> each) {
        return each.stream().allMatch(NormalReturn::of);
    }

    private NormalReturn() {}
}
