package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The bottom an empty collection literal carries, and how a concrete type replaces it.
 *
 * <p>`[]`, `Map.empty()` and `Set.empty()` have no element type of their own (ADR-0028), so they
 * type at a bottom that a later step refines: a fold seeded with `[]` learns its accumulator from
 * what the step returns, and a branch that yields an empty collection absorbs into the branch that
 * yields a populated one.
 */
public final class BottomInfer {

    private BottomInfer() {}

    /** Refines the type-variable bindings from a function argument's actual result: where the
     * function's declared result is a type variable and its current binding is unknown or an
     * empty-collection bottom, replace it with the concrete result the step grows. This is how a
     * {@code foldFrom} seeded with {@code []} recovers its accumulator type — the block returns the
     * grown list, not the bottom the seed carried. A composite result (a tuple of accumulators, as
     * {@code partition}/{@code distinct} fold) refines position by position. */
    public static void refineBottom(Type declaredResult, Type got, Map<String, Type> bind) {
        if (declaredResult instanceof Type.Var v) {
            Type cur = bind.get(v.name());
            if ((cur == null || Type.mentions(cur, BottomInfer::isBottom))
                    && !Type.mentions(got, BottomInfer::isBottom)) {
                bind.put(v.name(), got);
            }
        } else if (declaredResult instanceof Type.TupleOf dt && got instanceof Type.TupleOf gt
                && dt.elements().size() == gt.elements().size()) {
            for (int i = 0; i < dt.elements().size(); i++) {
                refineBottom(dt.elements().get(i), gt.elements().get(i), bind);
            }
        }
    }

    /** Reconciles two joined positions ({@code if} branches, {@code match} arms) where one may carry
     * an empty-collection bottom: the bottom takes on the other side's type (ADR-0028). It recurses
     * through every container, so a {@code Set.empty()} accumulator returned bare on one branch joins
     * with the {@code Set<Int>} the other grows, and a {@code (Set.empty(), [])} accumulator joins
     * position by position (the {@code distinct}/{@code partition} shape). Returns {@code null} when
     * the two do not reconcile, so the caller falls through to its ordinary rules — widening two
     * data-like types to their union, or reporting the disagreement. */
    static Type absorbBottom(Type a, Type b) {
        if (a.equals(b)) {
            return a;
        }
        if (isBottom(a)) {
            return b;
        }
        if (isBottom(b)) {
            return a;
        }
        if (a instanceof Type.ListOf la && b instanceof Type.ListOf lb) {
            Type e = absorbBottom(la.element(), lb.element());
            return e == null ? null : Type.list(e);
        }
        if (a instanceof Type.SetOf sa && b instanceof Type.SetOf sb) {
            Type e = absorbBottom(sa.element(), sb.element());
            return e == null ? null : Type.set(e);
        }
        if (a instanceof Type.OptionOf oa && b instanceof Type.OptionOf ob) {
            Type e = absorbBottom(oa.element(), ob.element());
            return e == null ? null : Type.option(e);
        }
        if (a instanceof Type.MapOf ma && b instanceof Type.MapOf mb) {
            Type k = absorbBottom(ma.key(), mb.key());
            Type v = absorbBottom(ma.value(), mb.value());
            return k == null || v == null ? null : Type.map(k, v);
        }
        if (a instanceof Type.TupleOf ta && b instanceof Type.TupleOf tb
                && ta.elements().size() == tb.elements().size()) {
            List<Type> elems = new ArrayList<>();
            for (int i = 0; i < ta.elements().size(); i++) {
                Type e = absorbBottom(ta.elements().get(i), tb.elements().get(i));
                if (e == null) {
                    return null;
                }
                elems.add(e);
            }
            return Type.tuple(elems);
        }
        return null;
    }

    /** The scalar empty-collection bottom: the element type of a {@code []} whose type is not yet
     * fixed (ADR-0028). It unifies with any type, so a comparison against it is left to run time. */
    static boolean isBottom(Type t) {
        return t instanceof Type.Nothing;
    }

    /** A syntactic empty-collection literal — {@code []}, {@code Map.empty()}, {@code Set.empty()} —
     * whose element/value type is fixed by context rather than written. */
    static boolean isEmptyCollectionLiteral(Ast.Expr e) {
        return (e instanceof Ast.ListLit l && l.elements().isEmpty())
                || (e instanceof Ast.Call c && c.args().isEmpty()
                        && (c.fn().equals("Map.empty") || c.fn().equals("Set.empty")));
    }

    /** Best-effort: bind the type variables of {@code result} from an {@code expected} type the context
     * pushed down, into {@code bind}. Unifies into a scratch copy and merges only on success, so an
     * expected type that does not fit the result leaves {@code bind} untouched and the ordinary checks
     * report the mismatch rather than this throwing early. Shared by the checker's call typing and the
     * backend's fold materialisation so both pin the same accumulator type (issue #70). */
    public static void pinResultTypeVars(Type result, Type expected, Map<String, Type> bind,
                                         Symbols symbols, SourcePos pos, String what) {
        if (expected == null) {
            return;
        }
        Map<String, Type> probe = new HashMap<>(bind);
        try {
            TypeOps.unify(result, expected, probe, symbols, pos, what);
            bind.putAll(probe);
        } catch (CompileException _) {
            // the expected type does not fit this result; leave bind untouched
        }
    }

    /** Whether a step-typing error is the unresolved-bottom error (an operand/branch reported as the
     * bottom marker {@code _}), as opposed to an unrelated failure. The bottom renders as a standalone
     * {@code _} token; a type merely named with an underscore ({@code My_Type}) does not match. */
    static boolean reportsUnresolvedBottom(CompileException e) {
        Diagnostic d = e.diagnostic();
        if (d == null) {
            return false;
        }
        String marker = Type.show(Type.NOTHING);   // "_"
        java.util.regex.Pattern standalone =
                java.util.regex.Pattern.compile("(^|[^\\p{Alnum}])" + marker + "([^\\p{Alnum}]|$)");
        if (d.diff() != null
                && (standalone.matcher(d.diff().actualType()).find()
                        || standalone.matcher(d.diff().expectedType()).find())) {
            return true;
        }
        if (d.args() != null) {
            for (Object a : d.args()) {
                if (a != null && standalone.matcher(a.toString()).find()) {
                    return true;
                }
            }
        }
        return false;
    }

    /** The fold seed argument when it is an un-inferrable empty-collection literal — a genuine fold
     * whose accumulator element type nothing has fixed — or {@code -1} otherwise. Used to point a
     * step-typing failure at the seed rather than deep inside the step. Two guards keep this to real
     * fold seeds so a non-fold call is never mis-reported as one (issue #70 review):
     *
     * <ul>
     *   <li>the signature is fold-shaped — a step function at index 0 and, at the seed index 1, an
     *       accumulator whose type is the fold's result. A higher-order function that merely takes a
     *       closure and an empty collection ({@code List.map}/{@code filter} over {@code []}) does not
     *       match, so its step failure is not relabelled as a fold-seed error; and</li>
     *   <li>the seed's source position differs from the call's. A combinator inlined onto its call
     *       site (e.g. {@code List.map}'s internal {@code []} accumulator, which desugars to a
     *       {@code List.foldFrom}) carries the call's own position; the caller never wrote an empty
     *       seed there, so it is excluded.</li>
     * </ul>
     */
    static int untypedEmptySeed(List<Ast.Expr> args, Type.FnOf fn, Map<String, Type> bind,
                                        SourcePos callPos) {
        int seed = 1;
        if (fn.params().size() <= seed || args.size() <= seed) {
            return -1;
        }
        boolean foldShaped = fn.params().get(0) instanceof Type.FnOf
                && !(fn.params().get(seed) instanceof Type.FnOf)
                && fn.params().get(seed).equals(fn.result());
        if (foldShaped
                && isEmptyCollectionLiteral(args.get(seed))
                && !args.get(seed).pos().equals(callPos)
                && Type.mentions(TypeOps.substitute(fn.params().get(seed), bind), BottomInfer::isBottom)) {
            return seed;
        }
        return -1;
    }

    /** Reads a bottom ({@code Nothing}) as the empty list — its run-time value when it is a list read
     * from an accumulator an empty collection seed grows (see the {@code CONCAT} case). Leaves any
     * other type untouched. */
    static Type bottomAsEmptyList(Type t) {
        return isBottom(t) ? Type.EMPTY_LIST : t;
    }

    /** The common element type of two list positions: identical types collapse; two data-like
     * types widen to the union of their cases (so {@code [High] ++ [LowRole]} is a list of both). */
    static Type unifyElem(Type a, Type b, SourcePos pos) {
        if (a == Type.NOTHING) {   // the empty list absorbs into the other's element type (ADR-0028)
            return b;
        }
        if (b == Type.NOTHING) {
            return a;
        }
        if (a.equals(b)) {
            return a;
        }
        if (TypeOps.isDataLike(a) && TypeOps.isDataLike(b)) {
            Set<TypeName> names = new HashSet<>(TypeOps.namesOf(a));
            names.addAll(TypeOps.namesOf(b));
            return Type.union(names);
        }
        throw CompileException.of(
                Diagnostic.of(null, "check.list.msg")
                        .title("check.list.title")
                        .at(pos)
                        .hint("check.list.hint", Type.show(a), Type.show(b))
                        .build(),
                "list elements disagree on type: " + a + " vs " + b);
    }
}
