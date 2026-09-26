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
     * What each binding read came to.
     *
     * <p>Every binding, however it was answered. A binding has one value and one environment it was
     * written in, whether the tree still holds the binding or the reading was told about it, so a
     * second read of a name is the first read asked again and what it comes to cannot differ. Held
     * for the length of one walk, because what is held is this walk's interpretation of a
     * denotation and not the denotation (ADR-0111).
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
        // A constant is the value it is whatever type it stands as.
        return switch (Core.withoutStanding(e)) {
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

    /**
     * What the name {@code r} reads comes to — from the binding the tree holds, or from what the
     * reading was told where the clause's shape consumed it.
     *
     * <p>Two places a binding is answered from and one reading of the answer. Which of the two
     * holds it is a fact about how far the tree was rewritten before this walk met it, and not
     * about the name: a binding has one value either way, so a name read twice is folded once
     * whichever place answered it.
     *
     * <p>And each is read under the environment its value was written in. A binding the tree holds
     * carries that environment with it; one the reading was told about was written where the
     * reading was told, and the names in it are answered by the reading again — not by whatever
     * the tree happens to bind around the place the name is read.
     */
    private Optional<Object> given(Core.Read r, Env env) {
        Optional<Object> already = folded.get(r.binding());
        if (already != null) {
            return already;
        }
        Bound bound = env.read(r.binding());
        Core value = bound == null ? at.valueOf(r.binding()) : bound.value();
        if (value == null) {
            return Optional.empty();
        }
        // Put before the fold as "not a constant", so a binding that reaches itself answers rather
        // than going round.
        folded.put(r.binding(), Optional.empty());
        Optional<Object> answer = eval(value, bound == null ? Env.NONE : bound.at());
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
        // A pattern is not folded to text and read again: the checker read it where it settled the
        // call, and what it means is on the call. Only the subject is folded, which is the last
        // argument (spec §pipe).
        if (call.settled() instanceof Core.KernelFact.StringMatches settled) {
            return eval(call.args().getLast(), env).orElse(null) instanceof String subject
                    ? ConstantAlgebra.matching(settled.meaning(), subject) : Optional.empty();
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
