package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What a checked expression comes to at compile time, read on the tree the rules are discharged
 * over.
 *
 * <p>Beside {@link ConstEval} and not instead of it. The same question is asked of a body twice —
 * where it is checked, which is {@code Hir}, and where its rules are discharged, which is
 * {@code Core} — and the two trees are two shapes. What an operator makes of the values under it is
 * neither shape's: it is {@link ConstantAlgebra}, which both ask, so a program cannot fold one way
 * at the check and another at the discharge.
 *
 * <p><b>It reads the graph rather than rebuilding a tree from it.</b> A binding is an edge, and a
 * name is followed to what it was given — from the binding standing in the tree, or from the
 * reading's own environment where the shape of the clause consumed it ({@link ClauseExpr.Scoped}).
 * Writing the value back out as syntax first and folding that is the same answer reached by copying
 * the body once per reference, which is what makes a name read twice cost twice.
 *
 * <p>Read where the name is read (ADR-0106, ADR-0111): a binding the expression never reads is
 * never folded, and a binding read more than once is folded once.
 */
final class CoreConstantEval {

    private final Symbols symbols;

    /** What the reading was told a name was given, where the binding is no longer in the tree. */
    private final Denotations at;

    /**
     * What each binding standing in the tree came to.
     *
     * <p>Only those: a binding the tree holds has one value and one environment it was written in,
     * so what it comes to is the same wherever it is read. One the environment answers for was
     * written somewhere this walk cannot see, and is read again rather than assumed to be the same
     * question.
     */
    private final Map<BindingId, Optional<Object>> folded = new HashMap<>();

    private CoreConstantEval(Symbols symbols, Denotations at) {
        this.symbols = symbols;
        this.at = at;
    }

    /** Folding against the library {@code symbols} names, under what {@code at} says a name was
     *  given. */
    static CoreConstantEval against(Symbols symbols, Denotations at) {
        return new CoreConstantEval(symbols, at);
    }

    /** What a name in force stands for: the value it was given, and the bindings that value is read
     *  under. The environment travels with the value, because a value stands for the name in the
     *  environment the binding was made in (ADR-0111). */
    private record Bound(Core value, Env at) {}

    /** The bindings the tree wrote, innermost first. */
    private record Env(BindingId binding, Bound bound, Env outer) {

        static final Env NONE = new Env(null, null, null);

        Env with(BindingId id, Core value, Env definedAt) {
            return new Env(id, new Bound(value, definedAt), this);
        }

        Bound read(BindingId id) {
            for (Env each = this; each != null; each = each.outer()) {
                if (id.equals(each.binding())) {
                    return each.bound();
                }
            }
            return null;
        }
    }

    /** What {@code e} folds to, or empty where it is not a compile-time constant. */
    Optional<Object> eval(Core e) {
        return eval(e, Env.NONE);
    }

    private Optional<Object> eval(Core e, Env env) {
        return switch (e) {
            case Core.Int i -> Optional.of(i.value());
            case Core.Decimal d -> Optional.of(d.value());
            case Core.Str s -> Optional.of(s.value());
            case Core.Bool b -> Optional.of(b.value());
            case Core.Neg n -> ConstantAlgebra.negate(eval(n.operand(), env).orElse(null));
            case Core.Binary b -> binary(b, env);
            case Core.PreservedCall call -> call(call, env);
            // A binding is the value its body is, with the binder standing for what it was given.
            case Core.LetIn li -> eval(li.body(), env.with(li.binder().binding(), li.value(), env));
            case Core.Read r -> given(r, env);
            case null, default -> Optional.empty();
        };
    }

    /** What the name {@code r} reads comes to — from the binding the tree holds, or from what the
     *  reading was told where the clause's shape consumed it. */
    private Optional<Object> given(Core.Read r, Env env) {
        Bound bound = env.read(r.binding());
        if (bound == null) {
            Core told = at.valueOf(r.binding());
            return told == null ? Optional.empty() : eval(told, env);
        }
        Optional<Object> already = folded.get(r.binding());
        if (already != null) {
            return already;
        }
        // Put before the fold as "not a constant", so a binding that reaches itself answers rather
        // than going round.
        folded.put(r.binding(), Optional.empty());
        Optional<Object> answer = eval(bound.value(), bound.at());
        folded.put(r.binding(), answer);
        return answer;
    }

    private Optional<Object> binary(Core.Binary b, Env env) {
        Optional<Object> left = eval(b.left(), env);
        Optional<Object> settled = left.isEmpty() ? Optional.empty()
                : ConstantAlgebra.settledByTheLeft(b.op(), left.get());
        if (settled.isPresent()) {
            return settled;
        }
        Optional<Object> right = eval(b.right(), env);
        if (left.isEmpty() || right.isEmpty()) {
            return Optional.empty();
        }
        return ConstantAlgebra.binary(b.op(), left.get(), right.get());
    }

    private Optional<Object> call(Core.PreservedCall call, Env env) {
        if (!(call.operation() instanceof ValueName.Stdlib.Operation operation)) {
            return Optional.empty();
        }
        Kernel kernel = symbols.kernelOf(operation);
        if (kernel == null) {
            return Optional.empty();
        }
        List<Object> args = new ArrayList<>();
        for (Core arg : call.args()) {
            Object folds = eval(arg, env).orElse(null);
            if (folds == null) {
                return Optional.empty();
            }
            args.add(folds);
        }
        return ConstantAlgebra.computed(kernel, args);
    }
}
