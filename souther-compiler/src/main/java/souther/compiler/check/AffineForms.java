package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.numeric.NumericDomain.LinearForm;

import java.math.BigDecimal;

/**
 * Reading an expression as {@code const + Σ coef·atom}, over whatever a caller counts as an atom.
 *
 * <p>One walk over one grammar. The check reads a clause this way to discharge it, and the measure
 * reads a rule this way to find the line it draws; the two ask about different atoms — the check
 * names a subject of its own, the measure names a position of a behavior's input — and they are the
 * same arithmetic over the same tree. Written twice, the second copy read fewer shapes than the
 * first, and a rule the check enforced was one the measure reported as unread.
 *
 * <p><b>What differs between callers is what a leaf is, and that is all.</b> Which nodes compose —
 * a literal, a negation, {@code +}, {@code -}, a scalar multiply, a binding, a newtype's value read
 * off something that is not a place — is a fact about the language and belongs here. What one of the
 * leaves is called, and what a name means inside a binding, belong to the reader.
 *
 * <p>No leaf rule of its own, and no environment of its own. Both were what {@link Terms} used to
 * carry: a walk that answered a binder's reads with the form its value had is a second account of
 * what a name means, weaker than the environment's by exactly the values the arithmetic cannot read,
 * and inside a reduction's step it was the only account there was (#867).
 *
 * @param <A> what the caller calls an atom
 * @param <E> what the caller carries as it goes inside a binding
 */
public final class AffineForms {

    /** What the walk cannot compose out of parts, which is the caller's to answer. */
    public interface Leaves<A, E> {

        /** {@code e} as a form, where nothing here composes one: an atom, a value read through, or
         *  null where the caller can say nothing about it. */
        LinearForm<A> leafOf(Core e, E at);

        /** What {@code li}'s body is read in. The one place a binding is entered, so that what a
         *  name means is settled once and no reader interprets a binder for itself. */
        E inside(Core.LetIn li, E at);

        /**
         * Whether a field access is a newtype's value read off something that is not a place.
         *
         * <p>What it wraps is what it is, so such a read is the target itself. Whether the target is
         * a place is asked of what it denotes and not of how it is spelled: a name given a computed
         * value is no more a place than the call it was given, and asked by the spelling it came out
         * one — so a guard over the name settled nothing about a construction over the value (#676).
         */
        boolean readsThrough(Core.FieldAccess fa, E at);
    }

    /**
     * {@code raw} as an affine form, or null where this composes none and the caller's leaf rule
     * names nothing either.
     *
     * <p>A node this has a rule for and cannot compose is read as a leaf as well. Reading the
     * structure of a value and naming the value are two questions: a variable product is outside the
     * fragment, and it is still one value, so what a rule states of it is still about the thing the
     * clause reads. Answering the first question with {@code null} and never asking the second is
     * what made {@code a * b} name nothing where it is written and something where it is bound —
     * which is a name changing what can be said of an expression.
     */
    public static <A, E> LinearForm<A> of(Core raw, E at, Leaves<A, E> leaves) {
        Core e = Terms.asOperator(raw);
        if (e instanceof Core.PreservedCall || e instanceof Core.Call) {
            // A call that folds is the number it folds to. `String.length("1A")` is 2, and a clause
            // about it is decided rather than owed — the run-time check is not what should answer a
            // question the compiler has already computed.
            BigDecimal folded = Terms.constantNumber(e);
            if (folded != null) {
                return LinearForm.constant(folded);
            }
        }
        LinearForm<A> composed = composed(e, at, leaves);
        return composed != null ? composed : leaves.leafOf(e, at);
    }

    /** {@code e} read as arithmetic over what its parts answer, or null where this has no rule for
     *  it or the rule it has does not compose. */
    private static <A, E> LinearForm<A> composed(Core e, E at, Leaves<A, E> leaves) {
        return switch (e) {
            case Core.Int i -> LinearForm.constant(BigDecimal.valueOf(i.value()));
            case Core.Decimal d -> LinearForm.constant(d.value());
            case Core.Neg n -> Terms.negate(of(n.operand(), at, leaves));
            case Core.Binary b when b.op() == Hir.BinOp.ADD ->
                    Terms.add(of(b.left(), at, leaves), of(b.right(), at, leaves), false);
            case Core.Binary b when b.op() == Hir.BinOp.SUB ->
                    Terms.add(of(b.left(), at, leaves), of(b.right(), at, leaves), true);
            // A scalar multiply by a constant (`Amount * 2`) is linear; `/` and a variable product
            // are not — a divide truncates for `Int`, and a variable factor is non-linear — so those
            // come back here as one value rather than as arithmetic over two.
            case Core.Binary b when b.op() == Hir.BinOp.MUL ->
                    Terms.scale(of(b.left(), at, leaves), of(b.right(), at, leaves));
            case Core.FieldAccess fa when leaves.readsThrough(fa, at) -> of(fa.target(), at, leaves);
            // A binding an expansion introduced (`let $0_n = n.value in $0_n * 2`) is what a helper
            // becomes, so reading through it is reading what the author wrote at the call. Whether
            // what it holds is a number is not asked: a binding denotes what it was given whatever
            // kind of value that is, which is what makes the facts a walk recorded about the places
            // under it reach the step that reads them (#867).
            case Core.LetIn li -> of(li.body(), leaves.inside(li, at), leaves);
            default -> null;
        };
    }

    private AffineForms() {}
}
