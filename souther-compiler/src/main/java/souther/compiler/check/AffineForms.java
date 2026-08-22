package souther.compiler.check;

import souther.compiler.types.BinOp;
import souther.compiler.core.Core;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.types.BindingId;

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
 * <p><b>The grammar and the walk belong here.</b> Which nodes compose — a literal, a negation,
 * {@code +}, {@code -}, a scalar multiply, a binding, a newtype's value read off something that is
 * not a place — is a fact about the language. A caller supplies only the answers that depend on its
 * environment: what an otherwise-uncomposed value is called, what environment lies inside a binding,
 * and which source value a name denotes transparently.
 *
 * <p><b>A caller answers with a {@link Core} and never with a {@link LinearForm}.</b> That is what
 * keeps the environment's answers from becoming a second account of the arithmetic. This walk once
 * took a leaf rule that could answer a binder's reads with the form its value had — an account of
 * arithmetic standing in for an account of meaning, weaker than the environment's by exactly the
 * values the arithmetic cannot read, and inside a reduction's step the only account there was
 * (ADR-0106). {@link Reading#readThrough} puts back a way to reach what a name was given, and its
 * answer is an expression: a caller can say which value a name denotes and cannot say what the
 * arithmetic of it comes to, so reading that expression is this walk's and no one else's
 * (ADR-0111).
 *
 * @param <A> what the caller calls an atom
 * @param <E> what the caller carries as it goes inside a binding
 */
public final class AffineForms {

    /**
     * What a name was given, and what to read it in.
     *
     * <p>The environment comes with the value because the two belong together: a value stands for
     * the name in the environment the binding was made in, which is not always the one the name was
     * read in. Where a caller cannot tell the two apart it hands back the environment it was given
     * and says why — carried in the type either way, so the day they come apart there is one place
     * that answers for it.
     */
    public record ReadThrough<E>(Core value, E at) {}

    /**
     * The answers this walk asks its caller for: what depends on the caller's environment, and
     * nothing else.
     */
    public interface Reading<A, E> {

        /** {@code e} as a form, where nothing here composes one: an atom, a value read through, or
         *  null where the caller can say nothing about it. */
        LinearForm<A> leafOf(Core e, E at);

        /** What {@code li}'s body is read in. The one place a binding is entered, so that what a
         *  name means is settled once and no reader interprets a binder for itself. */
        E inside(Core.LetIn li, E at);

        /**
         * The value {@code read}'s name denotes, where the name and that value are one value — or
         * null where the name stands for something of its own and reading through it would say of
         * one value what was written about another.
         *
         * <p>Answered from the environment, which is what knows. A name is a place the caller's
         * seeding wrote about, or a position of a behavior's input, or an element an operation
         * handed out, or the expression it was given, and which of those it is decides whether
         * anything may stand where it stands. What is answered is the expression alone: what its
         * arithmetic comes to is read here, once, so no caller keeps a second account of it.
         */
        ReadThrough<E> readThrough(Core.Read read, E at);

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
    public static <A, E> LinearForm<A> of(Core raw, E at, Reading<A, E> reading) {
        return of(raw, at, reading, new java.util.HashSet<>());
    }

    /**
     * The same, through the names already being read through on the way here.
     *
     * <p>Three stages, in this order. What the language composes is read first; then what a name
     * denotes, which the environment answers and this reads; then what the caller calls the value.
     * The middle one is not composition — whether a name may be read through is the environment's
     * answer and not a rule of the grammar — and it is not a leaf either, since a leaf is what is
     * left when nothing can be read. Folded into either neighbour, the boundary between what the
     * language says and what a caller says stops being one a reader can see.
     */
    private static <A, E> LinearForm<A> of(Core raw, E at, Reading<A, E> reading,
                                           java.util.Set<BindingId> following) {
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
        LinearForm<A> composed = composed(e, at, reading, following);
        if (composed != null) {
            return composed;
        }
        LinearForm<A> denoted = read(e, at, reading, following);
        return denoted != null ? denoted : reading.leafOf(e, at);
    }

    /**
     * The form of what a name denotes, or null where it denotes nothing this may read.
     *
     * <p>A name is read through once on the way to a form. A binding holds one value, so a chain of
     * them ends on its own where each was made inside the last; where a caller's environment reaches
     * further than that — over a whole body rather than down a path — nothing about a binding says
     * so, and this is what says the walk stops rather than a comment claiming it cannot go round.
     * Lifted again once the name is behind the walk, so a form adding one name to itself still reads
     * both of them.
     */
    private static <A, E> LinearForm<A> read(Core e, E at, Reading<A, E> reading,
                                             java.util.Set<BindingId> following) {
        if (!(e instanceof Core.Read r)) {
            return null;
        }
        ReadThrough<E> through = reading.readThrough(r, at);
        if (through == null || through.value() == e || !following.add(r.binding())) {
            return null;
        }
        LinearForm<A> form = of(through.value(), through.at(), reading, following);
        following.remove(r.binding());
        return form;
    }

    /** {@code e} read as arithmetic over what its parts answer, or null where this has no rule for
     *  it or the rule it has does not compose. */
    private static <A, E> LinearForm<A> composed(Core e, E at, Reading<A, E> reading,
                                                 java.util.Set<BindingId> following) {
        return switch (e) {
            case Core.Int i -> LinearForm.constant(BigDecimal.valueOf(i.value()));
            case Core.Decimal d -> LinearForm.constant(d.value());
            case Core.Neg n -> Terms.negate(of(n.operand(), at, reading, following));
            case Core.Binary b when b.op() == BinOp.ADD ->
                    Terms.add(of(b.left(), at, reading, following),
                            of(b.right(), at, reading, following), false);
            case Core.Binary b when b.op() == BinOp.SUB ->
                    Terms.add(of(b.left(), at, reading, following),
                            of(b.right(), at, reading, following), true);
            // A scalar multiply by a constant (`Amount * 2`) is linear; `/` and a variable product
            // are not — a divide truncates for `Int`, and a variable factor is non-linear — so those
            // come back here as one value rather than as arithmetic over two.
            case Core.Binary b when b.op() == BinOp.MUL ->
                    Terms.scale(of(b.left(), at, reading, following),
                            of(b.right(), at, reading, following));
            case Core.FieldAccess fa when reading.readsThrough(fa, at) ->
                    of(fa.target(), at, reading, following);
            // A binding an expansion introduced (`let $0_n = n.value in $0_n * 2`) is what a helper
            // becomes, so reading through it is reading what the author wrote at the call. Whether
            // what it holds is a number is not asked: a binding denotes what it was given whatever
            // kind of value that is, which is what makes the facts a walk recorded about the places
            // under it reach the step that reads them (#867).
            case Core.LetIn li -> of(li.body(), reading.inside(li, at), reading, following);
            default -> null;
        };
    }

    private AffineForms() {}
}
