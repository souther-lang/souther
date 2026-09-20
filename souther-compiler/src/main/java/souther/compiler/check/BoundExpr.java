package souther.compiler.check;

import souther.compiler.ast.Hir;

/**
 * An expression and the environment it means something in.
 *
 * <p>What a semantic reader is handed, in place of a bare tree. A sub-expression taken from under a
 * binding means nothing on its own: the names in it stand for what the bindings above them gave,
 * and a reader given the node alone reads those names as standing for nothing. Handed the two
 * together, a caller that drops the environment has to say so.
 *
 * <p>The same shape the affine walk reads a name through
 * ({@code AffineForms.ReadThrough}), for the same reason (ADR-0111): a value stands for a name in
 * the environment the binding was made in, so the two travel together or the value is read against
 * the wrong names.
 *
 * @param expr the expression, which is syntax on its own
 * @param at   what the names in it were given
 */
public record BoundExpr(Hir.Expr expr, BoundValues at) {

    public BoundExpr {
        if (expr == null || at == null) {
            throw new IllegalArgumentException(
                    "an expression means something somewhere: " + expr + " at " + at);
        }
    }

    /** {@code expr} with nothing in force — a root, or an expression no binding stands over. */
    public static BoundExpr root(Hir.Expr expr) {
        return new BoundExpr(expr, BoundValues.NONE);
    }
}
