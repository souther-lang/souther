package souther.compiler.check;

import souther.compiler.types.BinOp;
import souther.compiler.core.Core;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.types.BindingId;

import java.math.BigDecimal;
import java.util.Map;

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
        return outcome(raw, at, reading) instanceof Outcome.Composed<A, E> composed
                ? composed.form() : null;
    }

    /**
     * What reading {@code raw} as a form came to, which is a form or the node that stopped it.
     *
     * <p>The node, because this walk is the only thing that knows. It met the expression that has no
     * rule here and gave up there; a reader handed nothing back had to work out afterwards what the
     * difficulty had been, and the only material it had was the shape of the whole side — so a rule
     * over an operation this reads perfectly well was blamed for a form it could not read beside it.
     *
     * <p>The deepest one, and the first met where a form has two parts. What a reader is sent to fix
     * is the expression nothing composed, and naming the sum above it names an expression that would
     * compose the moment its part did.
     */
    public static <A, E> Outcome<A, E> outcome(Core raw, E at, Reading<A, E> reading) {
        return of(raw, at, reading, new java.util.HashSet<>());
    }

    /**
     * A form, or where the reading of one stopped.
     *
     * <p>Two cases and not a form that may be missing. Whether an expression is arithmetic this
     * reads is an answer about the expression; handed back as an absence it became an answer about
     * this walk, which whoever asked then had to interpret.
     */
    public sealed interface Outcome<A, E> {

        /** The arithmetic, over whatever the caller calls an atom. */
        record Composed<A, E>(LinearForm<A> form) implements Outcome<A, E> {

            public Composed {
                java.util.Objects.requireNonNull(form, "a reading that composed one has a form");
            }
        }

        /**
         * The expression this has no rule for and the caller could not name either, and what it was
         * being read in.
         *
         * <p>The environment travels with the expression, for the reason {@link ReadThrough} says:
         * a value stands for a name in the environment the binding was made in, which is not always
         * the one the name was read in. A caller handed the expression alone read it again in
         * whatever it happened to hold, which is that reading being done twice and the second one
         * free to disagree — and the day the two environments come apart, silently.
         */
        record StoppedAt<A, E>(Core node, E at) implements Outcome<A, E> {

            public StoppedAt {
                java.util.Objects.requireNonNull(node, "a reading that stopped stopped somewhere");
                java.util.Objects.requireNonNull(at, "and was reading it in something");
            }
        }
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
    private static <A, E> Outcome<A, E> of(Core raw, E at, Reading<A, E> reading,
                                           java.util.Set<BindingId> following) {
        Core e = Terms.asOperator(raw);
        if (e instanceof Core.PreservedCall || e instanceof Core.Call) {
            // A call that folds is the number it folds to. `String.length("1A")` is 2, and a clause
            // about it is decided rather than owed — the run-time check is not what should answer a
            // question the compiler has already computed.
            BigDecimal folded = Terms.constantNumber(e);
            if (folded != null) {
                return new Outcome.Composed<>(LinearForm.constant(folded));
            }
        }
        // Where the reading stopped inside what this walk does compose, kept while the questions
        // below are still asked. A name over an expression nothing reads is still a name the caller
        // may have an atom for, and taking the stop as the answer here would put the leaf question
        // out of reach — which is a rule about what a name may stand for, not about arithmetic.
        Stop<A, E> stopped = new Stop<>();
        LinearForm<A> composed = composed(e, at, reading, following, stopped);
        if (composed != null) {
            return new Outcome.Composed<>(composed);
        }
        Outcome<A, E> denoted = read(e, at, reading, following);
        if (denoted instanceof Outcome.Composed<A, E> composedName) {
            return composedName;
        }
        // A name whose value this could not read is still a name the caller may have an atom for,
        // so the leaf question is asked either way. Where it has none, what stopped the reading is
        // what was found inside the name rather than the name — that is the expression with no rule
        // here, and the one an author would have to change.
        LinearForm<A> leaf = reading.leafOf(e, at);
        if (leaf != null) {
            return new Outcome.Composed<>(leaf);
        }
        // Nothing named it, so this is a stop — reported at the most particular expression that has
        // no rule here. A sum whose left term nothing reads is not what an author would change.
        if (stopped.at != null) {
            return stopped.at;
        }
        return denoted != null ? denoted : new Outcome.StoppedAt<>(e, at);
    }

    /** The first stop met inside what this walk composes, kept while the questions after it are
     *  still asked. */
    private static final class Stop<A, E> {
        private Outcome.StoppedAt<A, E> at;
    }

    /** The form {@code e} came to, or null where the reading stopped inside it. For the parts of a
     *  composition, whose own stop is the whole one. */
    private static <A, E> LinearForm<A> formOf(Core e, E at, Reading<A, E> reading,
                                               java.util.Set<BindingId> following,
                                               Stop<A, E> stopped) {
        Outcome<A, E> read = of(e, at, reading, following);
        if (read instanceof Outcome.StoppedAt<A, E> here) {
            if (stopped.at == null) {
                stopped.at = here;
            }
            return null;
        }
        return ((Outcome.Composed<A, E>) read).form();
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
    private static <A, E> Outcome<A, E> read(Core e, E at, Reading<A, E> reading,
                                             java.util.Set<BindingId> following) {
        if (!(e instanceof Core.Read r)) {
            return null;
        }
        ReadThrough<E> through = reading.readThrough(r, at);
        if (through == null || through.value() == e || !following.add(r.binding())) {
            return null;
        }
        Outcome<A, E> form = of(through.value(), through.at(), reading, following);
        following.remove(r.binding());
        return form;
    }

    /** {@code e} read as arithmetic over what its parts answer, or null where this has no rule for
     *  it or the rule it has does not compose. */
    private static <A, E> LinearForm<A> composed(Core e, E at, Reading<A, E> reading,
                                                 java.util.Set<BindingId> following,
                                                 Stop<A, E> stopped) {
        return switch (e) {
            case Core.Int i -> LinearForm.constant(BigDecimal.valueOf(i.value()));
            case Core.Decimal d -> LinearForm.constant(d.value());
            case Core.Neg n -> Terms.negate(formOf(n.operand(), at, reading, following, stopped));
            case Core.Binary b when b.op() == BinOp.ADD ->
                    Terms.add(formOf(b.left(), at, reading, following, stopped),
                            formOf(b.right(), at, reading, following, stopped), false);
            case Core.Binary b when b.op() == BinOp.SUB ->
                    Terms.add(formOf(b.left(), at, reading, following, stopped),
                            formOf(b.right(), at, reading, following, stopped), true);
            // A scalar multiply by a constant (`Amount * 2`) is linear; `/` and a variable product
            // are not — a divide truncates for `Int`, and a variable factor is non-linear — so those
            // come back here as one value rather than as arithmetic over two.
            case Core.Binary b when b.op() == BinOp.MUL ->
                    Terms.scale(formOf(b.left(), at, reading, following, stopped),
                            formOf(b.right(), at, reading, following, stopped));
            // An operation the library says answers arithmetic over what it was given is that
            // arithmetic here: `Decimal.fromInt(n)` is `n`, `Date.daysBetween(a, b)` is `b - a`,
            // and a rule about the arguments is a rule about the call. Composed here beside the
            // operators, because that is what such an operation is — read at either caller's leaf
            // instead, one of the two would have it and a statement the model makes would be
            // measured by one reader and not the other.
            case Core.PreservedCall _ when formSaidOf(e) != null ->
                    answered(e, at, reading, following, stopped);
            case Core.Call _ when formSaidOf(e) != null ->
                    answered(e, at, reading, following, stopped);
            case Core.FieldAccess fa when reading.readsThrough(fa, at) ->
                    formOf(fa.target(), at, reading, following, stopped);
            // A binding an expansion introduced (`let $0_n = n.value in $0_n * 2`) is what a helper
            // becomes, so reading through it is reading what the author wrote at the call. Whether
            // what it holds is a number is not asked: a binding denotes what it was given whatever
            // kind of value that is, which is what makes the facts a walk recorded about the places
            // under it reach the step that reads them (#867).
            case Core.LetIn li -> formOf(li.body(), reading.inside(li, at), reading, following,
                    stopped);
            default -> null;
        };
    }

    /**
     * {@code call} read as the form the library says it answers, or null where one of the arguments
     * it is written over does not compose.
     *
     * <p>Over what each argument is counted as, which is the form that argument itself reads as
     * here. So a shift of a position by a written number and a shift of one position by another are
     * one rule with two readings, and neither is a case anybody wrote.
     */
    private static <A, E> LinearForm<A> answered(Core call, E at, Reading<A, E> reading,
                                                 java.util.Set<BindingId> following,
                                                 Stop<A, E> stopped) {
        LinearForm<souther.compiler.semantics.ArgumentRef> says = formSaidOf(call);
        java.util.List<Core> args = Terms.argsOf(call);
        // The expansion's own stops, kept off the walk's. What is inside a declared form is not
        // what an author wrote: the arguments stand where they stand because the library says the
        // operation answers this much of them, and a reader that cannot carry one of them has not
        // met an expression an author would change — it has met this call.
        Stop<A, E> inside = new Stop<>();
        LinearForm<A> form = LinearForm.constant(says.constant());
        for (Map.Entry<souther.compiler.semantics.ArgumentRef, BigDecimal> each
                : says.coefs().entrySet()) {
            int position = CallArguments.positionIn(each.getKey(), Terms.operationOf(call));
            if (position < 0 || position >= args.size()) {
                return stoppedAtTheCall(call, at, stopped);
            }
            LinearForm<A> argument = formOf(args.get(position), at, reading, following, inside);
            if (argument == null) {
                return stoppedAtTheCall(call, at, stopped);
            }
            form = form.plus(argument.times(each.getValue()));
        }
        return form;
    }

    /**
     * No form, and the call recorded as where the reading stopped.
     *
     * <p>The call and not what was found inside it. A stop is reported at the most particular
     * expression with no rule here, which is what an author would change — and inside a form the
     * library declares there is no such expression: the author wrote the call. Reported from
     * within, a rule over what {@code Date.daysBetween} answers came back as a rule about the field
     * the expansion reached, which is a rule the model does not state and a spelling nobody wrote.
     */
    private static <A, E> LinearForm<A> stoppedAtTheCall(Core call, E at, Stop<A, E> stopped) {
        if (stopped.at == null) {
            stopped.at = new Outcome.StoppedAt<>(call, at);
        }
        return null;
    }

    /**
     * What the library says {@code e} answers in what it was given, or null where it says nothing —
     * including where {@code e} is no call at all.
     *
     * <p>Asked of the operation the call resolved to and not of which of the two shapes of call node
     * it is. A body that runs holds a library call one way and the tree a declaration's rules are
     * read in holds it another, and the fact is about the operation either way; read off one shape,
     * the same statement would be composed in one representation and left a leaf in the other.
     */
    private static LinearForm<souther.compiler.semantics.ArgumentRef> formSaidOf(Core e) {
        souther.compiler.types.ValueName operation = Terms.operationOf(e);
        return operation == null ? null : DischargeRules.answersAFormOf(operation);
    }

    private AffineForms() {}
}
