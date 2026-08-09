package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * The bottom an empty collection literal carries, and how a concrete type replaces it.
 *
 * <p>`[]`, `Map.empty` and `Set.empty` have no element type of their own (ADR-0028), so they
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

    /** The scalar empty-collection bottom: the element type of a {@code []} whose type is not yet
     * fixed (ADR-0028). It unifies with any type, so a comparison against it is left to run time. */
    static boolean isBottom(Type t) {
        return t instanceof Type.Nothing;
    }

    /**
     * Whether {@code t} answers no value, so nothing about a value follows from standing beside it:
     * the bottom an empty collection carries, the {@link Type.Never} an {@code unreachable} answers
     * with, and the {@link Type.Erroneous} an error already reported stands in for.
     *
     * <p>These are the types that fit every expectation because they state nothing, which is the
     * opposite of what a type read off a position has to do. A reader asking "does this position say
     * what the value is" asks this and takes the answer's negation — it is the one place that decides
     * which types carry no information, so a type added with that property is added here rather than
     * in each reader's own exclusion list.
     */
    static boolean answersNoValue(Type t) {
        return t instanceof Type.Nothing || t instanceof Type.Never || t instanceof Type.Erroneous;
    }

    /**
     * An empty collection whose element/value type is fixed by context rather than written: the
     * literal {@code []}, and a library value that takes no argument to learn its type from.
     *
     * <p>Which library names those are is the library's to say, so this asks what the name denotes
     * and whether its declaration was written with a parameter list — not how it was spelled.
     */
    static boolean isEmptyCollectionLiteral(Ast.Expr e) {
        if (e instanceof Ast.ListLit l) {
            return l.elements().isEmpty();
        }
        return e instanceof Ast.Var v && v.denotes() instanceof ValueName.Stdlib lib
                && Prelude.isEmptyCollectionValue(lib.qualified());
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

    /** The common element type of two list positions — {@link TypeOps#join}, reported as a list
     * element rather than as a branch: identical types collapse, two data-like types widen to the
     * union of their cases (so {@code [High] ++ [LowRole]} is a list of both), and a list of each
     * widens the same way one level in. */
    static Type unifyElem(Type a, Type b, SourcePos pos) {
        Type joined = TypeOps.join(a, b);
        if (joined != null) {
            return joined;
        }
        throw CompileException.of(Diagnostic.of(DiagnosticCode.E1318, "check.list.msg")
                        .at(pos)
                        .hint("check.list.hint", Type.show(a), Type.show(b))
                        .build());
    }
}
