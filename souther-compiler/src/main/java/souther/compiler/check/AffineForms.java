package souther.compiler.check;

import souther.compiler.types.BinOp;
import souther.compiler.core.Core;
import souther.compiler.core.IntNegation;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.semantics.WhereAnOperatorAnswers;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.function.BiFunction;

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
 * {@code +}, {@code -}, a scalar multiply, a quotient by a constant, a binding, a construction of a
 * newtype, and an elimination standing against the introduction that wrote what it reads — is a
 * fact about the language. A caller supplies only the answers that depend on its
 * environment: what an otherwise-uncomposed value is called, what environment lies inside a binding,
 * and which source value a name denotes transparently.
 *
 * <p><b>A caller answers with a {@link Core} and never with a {@link LinearForm}.</b> That is what
 * keeps the environment's answers from becoming a second account of the arithmetic. This walk once
 * took a leaf rule that could answer a binder's reads with the form its value had — an account of
 * arithmetic standing in for an account of meaning, weaker than the environment's by exactly the
 * values the arithmetic cannot read, and inside a reduction's step the only account there was
 * (ADR-0106). {@link ValueStanding.Names#readThrough} puts back a way to reach what a name was given, and its
 * answer is an expression: a caller can say which value a name denotes and cannot say what the
 * arithmetic of it comes to, so reading that expression is this walk's and no one else's
 * (ADR-0111).
 *
 * <p>Two things are the caller's throughout, and every reading and every walk below is written over
 * them: {@code A} is what the caller calls an atom, and {@code E} is what it carries as it goes
 * inside a binding. Neither is declared here — this class holds no state — so each of
 * {@link Reading} and the walks says them for itself.
 */
public final class AffineForms {

    /**
     * The answers this walk asks its caller for: what depends on the caller's environment, and
     * nothing else.
     *
     * <p>How far a value is followed before it is read is {@link ValueStanding}'s, over the answers
     * about names this gives; what the value it ends at comes to is this walk's.
     */
    public interface Reading<A, E> extends ValueStanding.Names<E, Reading<A, E>> {

        /** The symbols the expression being read was resolved against. A call folds to a number
         *  when it computes one, which is a fact about the library, so the walk asks the caller
         *  rather than reaching for a library of its own. */
        Symbols symbols();

        /** What is asked of the declarations the expression was written against. Asked beside the
         *  symbols because what a carrier is depends on which of them is a sum, what its cases are,
         *  which enumerations list a case and what a name wraps, and those are the declarations'
         *  own answers rather than the tree they were written in. */
        DeclarationAccess declarations();

        /** {@code e} as a form, where nothing here composes one: an atom, a value read through, or
         *  null where the caller can say nothing about it. */
        LinearForm<A> leafOf(Core e, E at);

        /**
         * The same, told where the reading of what {@code e} is made of stopped — null where it
         * did not — so a caller naming the value by its binding can say why its number is none of
         * its own without reading the value again.
         */
        default LinearForm<A> leafOf(Core e, E at, Outcome.StoppedAt<A, E> inside) {
            return leafOf(e, at);
        }

        @Override
        default Reading<A, E> oneAtATime() {
            return new OneAtATime<>(this);
        }

        /**
         * The form of the values it was given the environment takes the call {@code node} as —
         * what the case of an operation's definition a reading is on answers — or null where it
         * takes it as none. The call is then that arithmetic over what it was given, as an
         * operation the library says answers a form of its arguments is.
         */
        default LinearForm<Core> takenAsAForm(Core node, E at) {
            return null;
        }

        /**
         * The product of two forms each with an atom in it, which the arithmetic composes none of,
         * where what the caller's atoms are makes it one — or null where they do not, and the
         * product is the operation no form says.
         *
         * <p>Asked only after the arithmetic's own rule has refused, of the two forms it read: a
         * product with a constant on either side is the arithmetic's, and a caller never says it
         * again.
         */
        default LinearForm<A> productOf(LinearForm<A> left, LinearForm<A> right) {
            return null;
        }

        /**
         * That the walk composed {@code operation} — a sum, a difference, a product or a negation
         * an operator writes — into {@code form}, for a caller that reads where each operator a
         * value is worked out through answers ({@link WhereAnOperatorAnswers}). What the walk
         * composes is not changed by it.
         *
         * <p>Told of each operator and not only of the whole: {@code (a + b) - b} comes to
         * {@code a}, and a run stops at {@code a + b} all the same.
         */
        default void composed(Core operation, LinearForm<A> form) {
        }

        /**
         * Whether a field access is a newtype's value read off something that is not a place.
         *
         * <p>What it wraps is what it is, so such a read is the target itself. Whether the target is
         * a place is asked of what it denotes and not of how it is spelled: a name given a computed
         * value is no more a place than the call it was given, and asked by the spelling it came out
         * one — so a guard over the name settled nothing about a construction over the value.
         *
         * <p><b>The second proof a projection has, and asked second.</b> Where the value read from
         * was written down, this walk takes the field off the construction that gave it and never
         * asks here. What is left for this is a projection with no construction in sight — a name a
         * call was given — which is a different piece of evidence and not a weaker copy of the
         * first. Asked first, it would answer a projection the grammar reads, and the grammar's
         * rule could be taken away without anything saying so.
         */
        boolean readsThrough(Core.FieldAccess fa, E at);
    }

    /**
     * Whether two readings came to the same form.
     *
     * <p>On the numbers and not on the records' own equality. A form is a constant and a coefficient
     * apiece, and {@code 0.10} and {@code 0.1} are one number — two readings differing in nothing
     * but a scale are not two answers, and compared by {@code equals} they would be.
     *
     * <p><b>Equal and never near.</b> What this decides is whether several values state one thing,
     * which is either so or not: a rule that answered with whatever two forms have in common would
     * be reading a weaker rule than the model states and reporting it as the model's. So there is no
     * order here for a caller to relax into, and a form that is not this one is no answer at all.
     */
    public static <A> boolean sameForm(LinearForm<A> a, LinearForm<A> b) {
        if (a.constant().compareTo(b.constant()) != 0
                || !a.coefs().keySet().equals(b.coefs().keySet())) {
            return false;
        }
        return a.coefs().entrySet().stream()
                .allMatch(one -> one.getValue().compareTo(b.coefs().get(one.getKey())) == 0);
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
        return of(raw, at, reading, new Walk<>());
    }

    /**
     * {@link #of(Core, Object, Reading)}, holding what each name came to in {@code answered}, which
     * the caller keeps for as long as it reads with {@code reading}.
     *
     * <p>For a reading that asks itself something while it reads — the fact an operation states of
     * its arguments, what a condition compares — so that a value it is part way through reading is
     * read once and not once per question. What is held is keyed by the value and the environment
     * it is read in ({@link BindingWalk}), so an answer is taken again only for the same question.
     */
    static <A, E> LinearForm<A> of(Core raw, E at, Reading<A, E> reading,
                                   BindingWalk.Answers<Outcome<A, E>> answered,
                                   FoldedValue.Kept<E> folds) {
        return of(raw, at, reading, new Walk<>(answered, folds))
                instanceof Outcome.Composed<A, E> composed ? composed.form() : null;
    }

    /** One walk of one expression, reading each name it meets once ({@link BindingWalk}). */
    private static final class Walk<A, E> extends BindingWalk<Outcome<A, E>> {

        /** What each name the folds met came to, kept by the caller beside what each name the walk
         *  read came to — or null where nobody keeps it, and each fold is its own. */
        private final FoldedValue.Kept<E> folds;

        Walk() {
            this.folds = null;
        }

        Walk(BindingWalk.Answers<Outcome<A, E>> answered, FoldedValue.Kept<E> folds) {
            super(answered);
            this.folds = folds;
        }
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
         * The expression the reading stopped at, what it was being read in, and why it stopped
         * there.
         *
         * <p>The environment travels with the expression, for the reason {@link ValueStanding.ReadThrough} says:
         * a value stands for a name in the environment the binding was made in, which is not always
         * the one the name was read in. A caller handed the expression alone read it again in
         * whatever it happened to hold, which is that reading being done twice and the second one
         * free to disagree — and the day the two environments come apart, silently.
         *
         * <p>And why travels with it for the same kind of reason: this walk is what decided it. A
         * caller that names a reason told from the kind of expression stopped at would be a second
         * account of the arithmetic, and one that tells a product of two unknowns from a sum whose
         * number has no representation only by guessing.
         */
        record StoppedAt<A, E>(Core node, E at, Halt<A, E> why) implements Outcome<A, E> {

            public StoppedAt {
                java.util.Objects.requireNonNull(node, "a reading that stopped stopped somewhere");
                java.util.Objects.requireNonNull(at, "and was reading it in something");
                Objects.requireNonNull(why, "and stopped for a reason");
            }
        }
    }

    /**
     * Why the walk stopped at an expression, from the closed set of ways it can.
     *
     * <p>Only the first is about the expression being one this walk has no words for. The rest are
     * expressions it has a rule for, under which the parts it read do not come to one form.
     */
    public sealed interface Halt<A, E> {

        /**
         * The arithmetic no form says that this stop comes to, through however many calls the
         * library states the form of it was reached under — or empty where it is another stop.
         *
         * <p>The one place a stop is asked this, so that a reader of a stop does not decide for
         * itself how far down to look.
         */
        default Optional<NonAffineOperation> nonAffineOperation() {
            Halt<A, E> at = this;
            while (at instanceof AnArgumentStopped<A, E>(var argument)) {
                at = argument.why();
            }
            return at instanceof NotLinear<A, E>(var operation)
                    ? Optional.of(operation) : Optional.empty();
        }

        /** No rule here for the expression, and the caller named it nothing. */
        record NoRule<A, E>() implements Halt<A, E> {}

        /** A product of two values neither of which is a constant, or a quotient by one that is
         *  not: arithmetic, and none a form over the atoms says. */
        record NotLinear<A, E>(NonAffineOperation operation) implements Halt<A, E> {}

        /** A quotient by nought or the least whole number negated, which no run has a number
         *  for: the run aborts there. */
        record NoNumberOnARun<A, E>() implements Halt<A, E> {}

        /** A number the arithmetic worked out exactly and could not hold. */
        record NotHeld<A, E>(UnheldNumber why) implements Halt<A, E> {

            public NotHeld {
                Objects.requireNonNull(why, "a number not held is not held for a reason");
            }
        }

        /** The values the expression can stand for, every one read, came to different forms. */
        record ValuesDisagree<A, E>() implements Halt<A, E> {}

        /**
         * An argument of a call the library says the form of did not compose; reported at the call,
         * which is what an author wrote, and stopped for what stopped the argument.
         */
        record AnArgumentStopped<A, E>(Outcome.StoppedAt<A, E> argument) implements Halt<A, E> {

            public AnArgumentStopped {
                Objects.requireNonNull(argument, "an argument stopped somewhere");
            }
        }
    }

    /**
     * The same, through the names already being read through on the way here.
     *
     * <p>Four stages, in this order. What the language composes is read first; then what the whole
     * expression comes to, where every part of it is written down; then what a name denotes, which
     * the environment answers and this reads; then what the caller calls the value. The third is
     * not composition — whether a name may be read through is the environment's answer and not a
     * rule of the grammar — and it is not a leaf either, since a leaf is what is left when nothing
     * can be read. Folded into either neighbour, the boundary between what the language says and
     * what a caller says stops being one a reader can see.
     *
     * <p>The second stands where it does because what an expression comes to is a question about
     * neither. It is not the grammar's, which reads arithmetic over positions and has no position
     * here to read; and it is not the caller's, since a number every part of which is written down
     * is that number whatever the caller would name. Asked before the grammar it would answer the
     * same and re-read every written sub-expression the arms compose without it; asked after the
     * environment it would be asked of expressions a name already answered for.
     */
    private static <A, E> Outcome<A, E> of(Core raw, E at, Reading<A, E> reading,
                                           Walk<A, E> following) {
        // A value the environment takes as another is that value, read where it is.
        ValueStanding.Standing<E, Reading<A, E>> taken = ValueStanding.taken(raw, at, reading);
        if (taken != null) {
            return of(taken.value(), taken.at(), reading, following);
        }
        Core e = Terms.asOperator(raw);
        // Where the reading stopped inside what this walk does compose, kept while the questions
        // below are still asked. A name over an expression nothing reads is still a name the caller
        // may have an atom for, and taking the stop as the answer here would put the leaf question
        // out of reach — which is a rule about what a name may stand for, not about arithmetic.
        Stop<A, E> stopped = new Stop<>();
        LinearForm<A> composed = composed(e, at, reading, following, stopped);
        if (composed != null) {
            return new Outcome.Composed<>(composed);
        }
        // An expression this composes nothing out of is still the number it folds to, where it
        // folds to one. `String.length("1A")` is 2, and a clause about it is decided rather than
        // owed — the run-time check is not what should answer a question the compiler has already
        // computed. What is asked here is a written decimal or a whole number, which is every
        // number a fold answers that the arms above do not: a fold comes to a fraction only through
        // the operators, and each of those is arithmetic this composes.
        BigDecimal folded = foldedNumber(e, at, reading, following);
        if (folded != null) {
            return new Outcome.Composed<>(
                    LinearForm.constant(ExactRatio.of(folded)));
        }
        Outcome<A, E> denoted = read(e, at, reading, following);
        if (denoted instanceof Outcome.Composed<A, E> composedName) {
            return composedName;
        }
        // A name whose value this could not read is still a name the caller may have an atom for,
        // so the leaf question is asked either way. Where it has none, what stopped the reading is
        // what was found inside the name rather than the name — that is the expression with no rule
        // here, and the one an author would have to change.
        LinearForm<A> leaf = reading.leafOf(e, at,
                denoted instanceof Outcome.StoppedAt<A, E> inside ? inside : stopped.at);
        if (leaf != null) {
            return new Outcome.Composed<>(leaf);
        }
        // Nothing named it, so this is a stop — reported at the most particular expression that has
        // no rule here. A sum whose left term nothing reads is not what an author would change.
        if (stopped.at != null) {
            return stopped.at;
        }
        return denoted != null ? denoted : new Outcome.StoppedAt<>(e, at, new Halt.NoRule<>());
    }

    /** The first stop met inside what this walk composes, kept while the questions after it are
     *  still asked. */
    private static final class Stop<A, E> {
        private Outcome.StoppedAt<A, E> at;
    }

    /** The form {@code e} came to, or null where the reading stopped inside it. For the parts of a
     *  composition, whose own stop is the whole one. */
    private static <A, E> LinearForm<A> formOf(Core e, E at, Reading<A, E> reading,
                                               Walk<A, E> following,
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
     *
     * <p>And a name the reading names every value of is read as what those values agree on. The same
     * step as the one above with the count changed: one value is what the name comes to, and several
     * come to whatever all of them come to.
     *
     * <p>Where a member stopped, that is where the reading stopped — as it is for the one value a
     * name denotes, since a member of a written list is an expression an author wrote and is the one
     * they would have to change. Where every member was read and they came to different forms,
     * nothing stopped and this answers nothing, and the stop is reported at the name.
     */
    private static <A, E> Outcome<A, E> read(Core written, E at, Reading<A, E> reading,
                                             Walk<A, E> following) {
        Core e = Core.withoutStanding(written);
        if (!(e instanceof Core.Read r)) {
            return null;
        }
        ValueStanding.Named<E, Reading<A, E>> led = ValueStanding.named(r, at, reading);
        if (led == null || !following.enter(r.binding())) {
            return null;
        }
        Outcome<A, E> read = switch (led) {
            // Asked once per question. What a name comes to is the value it was given read in the
            // environment it was given in, and a second occurrence of the name is that same
            // question — so the walk holds the answer rather than composing the value again.
            case ValueStanding.Named.One<E, Reading<A, E>>(
                    ValueStanding.Standing<E, Reading<A, E>> one) ->
                    following.readingOf(r.binding(), one.value(), one.at(),
                            () -> of(one.value(), one.at(), one.names(), following));
            case ValueStanding.Named.OneOf<E, Reading<A, E>>(
                    List<ValueStanding.Standing<E, Reading<A, E>>> members) -> {
                Stop<A, E> stopped = new Stop<>();
                LinearForm<A> agreed = commonForm(members, e, at, following, stopped);
                yield agreed != null ? new Outcome.Composed<>(agreed) : stopped.at;
            }
        };
        following.leave(r.binding());
        return read;
    }

    /** {@code of} with no plurality in it, which is what the members of one are read with. */
    private record OneAtATime<A, E>(Reading<A, E> of) implements Reading<A, E> {

        @Override
        public Reading<A, E> oneAtATime() {
            return this;
        }

        @Override
        public Symbols symbols() {
            return of.symbols();
        }

        @Override
        public DeclarationAccess declarations() {
            return of.declarations();
        }

        @Override
        public LinearForm<A> leafOf(Core e, E at) {
            return of.leafOf(e, at);
        }

        @Override
        public LinearForm<A> leafOf(Core e, E at, Outcome.StoppedAt<A, E> inside) {
            return of.leafOf(e, at, inside);
        }

        @Override
        public E inside(Core.LetIn li, E at) {
            return of.inside(li, at);
        }


        @Override
        public ValueStanding.ReadThrough<E> readThrough(Core.Read read, E at) {
            return of.readThrough(read, at);
        }

        @Override
        public List<ValueStanding.ReadThrough<E>> alternativesOf(Core.Read read, E at) {
            return null;
        }

        @Override
        public ValueStanding.ReadThrough<E> taken(Core node, E at) {
            return of.taken(node, at);
        }

        @Override
        public LinearForm<Core> takenAsAForm(Core node, E at) {
            return of.takenAsAForm(node, at);
        }

        @Override
        public LinearForm<A> productOf(LinearForm<A> left, LinearForm<A> right) {
            return of.productOf(left, right);
        }

        @Override
        public boolean readsThrough(Core.FieldAccess fa, E at) {
            return of.readsThrough(fa, at);
        }
    }

    /**
     * The one form every one of {@code these} comes to, or null where they do not all come to one.
     *
     * <p>What a rule about a position several values can stand at is entitled to say. Every value is
     * read, and what comes back is the form they support between them — which is a form they all
     * have or nothing. A reading that answered with one of them would state a hundred thousand for a
     * model that says a hundred thousand or two hundred thousand, and one that answered with what
     * two forms have in common would state a rule weaker than the model's and report it as the
     * model's.
     *
     * <p>Not a meet. There is no order being descended here and no weaker answer to fall back on:
     * the values agree or this walk has nothing to say about the position — and says so at
     * {@code e}, the expression that stands for all of them.
     */
    private static <A, E> LinearForm<A> commonForm(
            List<ValueStanding.Standing<E, Reading<A, E>>> these, Core e, E at,
            Walk<A, E> following, Stop<A, E> stopped) {
        LinearForm<A> agreed = null;
        for (ValueStanding.Standing<E, Reading<A, E>> each : these) {
            LinearForm<A> here =
                    formOf(each.value(), each.at(), each.names(), following, stopped);
            if (here == null) {
                return null;
            }
            if (agreed == null) {
                agreed = here;
            } else if (!sameForm(agreed, here)) {
                return halted(e, at, new Halt.ValuesDisagree<>(), stopped);
            }
        }
        return agreed;
    }

    /**
     * What an operator over the forms of its two parts comes to under its rule: the form, or null
     * with why there is none recorded at {@code e}. Null where a part is no form, whose stop is the
     * whole one.
     */
    private static <A, E> LinearForm<A> operated(
            Core e, E at, LinearForm<A> left, LinearForm<A> right,
            BiFunction<LinearForm<A>, LinearForm<A>, Terms.Operated<A>> rule, Stop<A, E> stopped) {
        if (left == null || right == null) {
            return null;
        }
        return switch (rule.apply(left, right)) {
            case Terms.Operated.Form<A>(LinearForm<A> form) -> form;
            case Terms.Operated.NotLinear<A>(NonAffineOperation operation) ->
                    halted(e, at, new Halt.NotLinear<>(operation), stopped);
            case Terms.Operated.NoNumberOnARun<A> _ ->
                    halted(e, at, new Halt.NoNumberOnARun<>(), stopped);
            case Terms.Operated.NotHeld<A>(UnheldNumber why) ->
                    halted(e, at, new Halt.NotHeld<>(why), stopped);
        };
    }

    /** The product of two forms by the arithmetic's rule, and where that rule finds no form, by
     *  what the caller's atoms say of it. */
    private static <A, E> Terms.Operated<A> productAsRead(LinearForm<A> left, LinearForm<A> right,
                                                          Reading<A, E> reading) {
        Terms.Operated<A> product = Terms.product(left, right);
        if (!(product instanceof Terms.Operated.NotLinear<A>)) {
            return product;
        }
        LinearForm<A> asked = reading.productOf(left, right);
        return asked == null ? product : new Terms.Operated.Form<>(asked);
    }

    /** Whether {@code call} is a floor remainder whose divisor is a form with a number of the
     *  input in it. */
    private static <A, E> boolean remainderByAValue(Core.PreservedCall call, E at,
                                                    Reading<A, E> reading, Walk<A, E> following) {
        OptionalInt divides =
                DefaultBoundOperationFacts.get().divisorOfAFloorRemainder(call.operation());
        return divides.isPresent() && call.args().size() > divides.getAsInt()
                && of(call.args().get(divides.getAsInt()), at, reading, following)
                        instanceof Outcome.Composed<A, E> composed
                && !composed.form().coefs().isEmpty();
    }

    /** {@code form}, with the reading told {@code operation} came to it ({@link Reading#composed})
     *  — where it came to one. */
    private static <A, E> LinearForm<A> told(Core operation, LinearForm<A> form,
                                             Reading<A, E> reading) {
        if (form != null) {
            reading.composed(operation, form);
        }
        return form;
    }

    /** No form, and {@code e} recorded as where the reading stopped and why — where nothing
     *  stopped it first. */
    private static <A, E> LinearForm<A> halted(Core e, E at, Halt<A, E> why, Stop<A, E> stopped) {
        if (stopped.at == null) {
            stopped.at = new Outcome.StoppedAt<>(e, at, why);
        }
        return null;
    }

    /** {@code e} read as arithmetic over what its parts answer, or null where this has no rule for
     *  it or the rule it has does not compose. */
    private static <A, E> LinearForm<A> composed(Core asPlaced, E at, Reading<A, E> reading,
                                                 Walk<A, E> following,
                                                 Stop<A, E> stopped) {
        Core e = Core.withoutStanding(asPlaced);
        LinearForm<A> written = literal(e, at, reading);
        if (written != null) {
            return written;
        }
        return switch (e) {
            // No number: the smallest Int negated is the run time's abort, and reading it as the
            // form of the operand negated would put a number there that no run has.
            case Core.Neg n when IntNegation.isTheLeastInt(n.operand()) ->
                    halted(e, at, new Halt.NoNumberOnARun<>(), stopped);
            case Core.Neg n -> told(n, Terms.negate(formOf(n.operand(), at, reading, following,
                    stopped)), reading);
            case Core.Binary b when b.op() == BinOp.ADD -> told(b,
                    operated(e, at, formOf(b.left(), at, reading, following, stopped),
                            formOf(b.right(), at, reading, following, stopped),
                            (left, right) -> Terms.sum(left, right, false), stopped), reading);
            case Core.Binary b when b.op() == BinOp.SUB -> told(b,
                    operated(e, at, formOf(b.left(), at, reading, following, stopped),
                            formOf(b.right(), at, reading, following, stopped),
                            (left, right) -> Terms.sum(left, right, true), stopped), reading);
            // A scalar multiply by a constant (`Amount * 2`) is linear and a variable factor is
            // not, so a product of two atoms comes back here as one value rather than as arithmetic
            // over two — unless the caller's atoms make it one (`Reading.productOf`).
            case Core.Binary b when b.op() == BinOp.MUL -> told(b,
                    operated(e, at, formOf(b.left(), at, reading, following, stopped),
                            formOf(b.right(), at, reading, following, stopped),
                            (left, right) -> productAsRead(left, right, reading), stopped),
                    reading);
            // And a quotient by a constant is that scalar multiply by the reciprocal. The quotient
            // is exact, so a third is what `x / 3` weighs its position by and not the nearest number
            // either operand's type writes — which is why this is arithmetic over a position at all
            // rather than a value whose fraction went somewhere the form could not say. Which
            // divisors are constant, and why `1 / x` is none of them, is `Terms.quotient`'s.
            case Core.Binary b when b.op() == BinOp.DIV ->
                    operated(e, at, formOf(b.left(), at, reading, following, stopped),
                            formOf(b.right(), at, reading, following, stopped), Terms::quotient,
                            stopped);
            // An operation the library says answers arithmetic over what it was given is that
            // arithmetic here: `Decimal.fromInt(n)` is `n`, `Date.daysBetween(a, b)` is `b - a`,
            // and a rule about the arguments is a rule about the call. Composed here beside the
            // operators, because that is what such an operation is — read at either caller's leaf
            // instead, one of the two would have it and a statement the model makes would be
            // measured by one reader and not the other.
            // And a call the environment takes as what a case of its operation's definition
            // answers is that arithmetic over the values it was given, on the reading that is on
            // the case.
            // What a division by a number a row writes leaves is a remainder with no period: the
            // values it holds of come round at a distance the row chooses, so it is arithmetic and
            // no form over the atoms says it. Said where it is met, as a product of two unknowns
            // is, and only where nothing names the call as an atom of its own.
            case Core.PreservedCall call when remainderByAValue(call, at, reading, following) ->
                    halted(e, at, new Halt.NotLinear<>(
                            NonAffineOperation.REMAINDER_BY_NON_CONSTANT_VALUE), stopped);
            case Core.PreservedCall _ when reading.takenAsAForm(e, at) != null ->
                    overTheValues(e, reading.takenAsAForm(e, at), at, reading, following, stopped);
            case Core.PreservedCall _ when formSaidOf(e) != null ->
                    answered(e, formSaidOf(e), at, reading, following, stopped);
            case Core.Call _ when formSaidOf(e) != null ->
                    answered(e, formSaidOf(e), at, reading, following, stopped);
            // A newtype's construction is the value it wraps. Whether the name is one is asked of
            // the reading of the position, which says the names a value is written under: a
            // newtype puts one there and a data of one field does not — that one wraps its value
            // rather than being it, and its construction is a value of its own. Asked of the
            // declarations again instead, this would be a second answer to how far a name reaches.
            // A carrier takes the same names off to find a value written down, and answers above
            // for `Yen(100)` before this is reached. The two agree where they overlap and are not
            // one rule: that one asks what a written value counts as and stops where nothing is
            // written, and this one asks what the arithmetic under the name comes to.
            case Core.Construct nd when !nd.values().isEmpty()
                    && TypeView.asWritten(Type.ref(nd.typeName()), reading.symbols(),
                            reading.declarations().kinds(), reading.declarations().sums())
                            .isWrapped() ->
                    formOf(nd.values().get(0).value(), at, reading, following, stopped);
            // One arm, holding two proofs that this projection is the value it reads. The
            // structural one is asked first and is asked as whether it produced a successor rather
            // than as what kind of node was standing there: a construction without the field asked
            // for has proved nothing, and read as a node kind it would take the answer away from
            // the proof that can still be made. Second, and only where nothing was written to
            // eliminate, the reading's own evidence that the projection keeps what it reads —
            // which is how a name a call was given is read through with no construction in sight.
            case Core.FieldAccess fa -> {
                List<ValueStanding.Standing<E, Reading<A, E>>> eliminated =
                        ValueStanding.eliminated(fa, at, reading, following);
                if (eliminated != null) {
                    yield commonForm(eliminated, e, at, following, stopped);
                }
                yield reading.readsThrough(fa, at)
                        ? formOf(fa.target(), at, reading, following, stopped) : null;
            }
            case Core.FieldProjection p -> projected(p, at, reading, following, stopped);
            // The same elimination against the introduction beside it. A tuple's element is reached
            // this way and no other — the language writes no projection of one, so what comes here
            // is what a binding over a tuple was taken apart into — and there is no second proof to
            // fall back on, because nothing declares a tuple transparent the way a newtype's
            // declaration does.
            case Core.TupleGet get -> {
                List<ValueStanding.Standing<E, Reading<A, E>>> eliminated =
                        ValueStanding.eliminated(get, at, reading, following);
                yield eliminated == null ? null
                        : commonForm(eliminated, e, at, following, stopped);
            }
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
     * {@code p} read as arithmetic: the arm above for a field access, asked of each of its names in
     * turn from the last one down.
     *
     * <p>The same two proofs in the same order. Where the second one holds, what the projection
     * comes to is what its target comes to, and the target is the projection one name shorter — so
     * the reading goes down a name and asks again, and only where it stops does it come back up,
     * each name it passed answering with what the one below it came to or, where that was nothing,
     * with what the walk makes of the name itself ({@link #unread}). That is the order the arm and
     * {@link #formOf} take when the names are written out; it is kept here and not on the stack,
     * because how many names there are is as long as the declarations chain.
     */
    private static <A, E> LinearForm<A> projected(Core.FieldProjection p, E at,
                                                  Reading<A, E> reading, Walk<A, E> following,
                                                  Stop<A, E> stopped) {
        // The projections the reading went down through, below `p`, and the stop each one's own
        // arm records — the first being the caller's.
        List<Core.FieldProjection> through = new ArrayList<>();
        List<Stop<A, E>> stops = new ArrayList<>();
        stops.add(stopped);
        Core.FieldProjection here = p;
        LinearForm<A> form;
        while (true) {
            Stop<A, E> stop = stops.getLast();
            // What a carrier counts a written value as is asked ahead of the arms, as it is for
            // any expression ({@link #composed}).
            LinearForm<A> written = literal(here, at, reading);
            if (written != null) {
                form = written;
                break;
            }
            List<ValueStanding.Standing<E, Reading<A, E>>> eliminated =
                    ValueStanding.eliminated(here, at, reading, following);
            if (eliminated != null) {
                form = commonForm(eliminated, here, at, following, stop);
                break;
            }
            if (!reading.readsThrough(here.lastAccess(), at)) {
                form = null;
                break;
            }
            if (!(here.target() instanceof Core.FieldProjection shorter)) {
                form = formOf(here.target(), at, reading, following, stop);
                break;
            }
            through.add(shorter);
            stops.add(new Stop<>());
            here = shorter;
        }
        // Back up the names gone down through: each one is read as the walk reads any expression,
        // which is its arm's form where there is one and what is left of the walk where not.
        for (int i = through.size() - 1; i >= 0; i--) {
            Outcome<A, E> read = form != null ? new Outcome.Composed<>(form)
                    : unread(through.get(i), at, reading, following, stops.get(i + 1));
            if (read instanceof Outcome.StoppedAt<A, E> stop) {
                if (stops.get(i).at == null) {
                    stops.get(i).at = stop;
                }
                form = null;
            } else {
                form = ((Outcome.Composed<A, E>) read).form();
            }
        }
        return form;
    }

    /** The number {@code e} folds to read in {@code at} with the reading's own names
     *  ({@link FoldedValue}), or null where it folds to none — with what each name came to kept
     *  where the walk's caller keeps it. */
    private static <A, E> BigDecimal foldedNumber(Core e, E at, Reading<A, E> reading,
                                                  Walk<A, E> following) {
        return FoldedValue.number(following.folds == null
                ? FoldedValue.of(e, at, reading, reading.symbols())
                : FoldedValue.of(e, at, reading, reading.symbols(), following.folds));
    }

    /**
     * What the walk makes of a projection its arm composed nothing for: the stages after
     * composition, in their order ({@link #of}). A projection is not a name, so the stage that
     * reads one through has nothing to ask.
     */
    private static <A, E> Outcome<A, E> unread(Core.FieldProjection p, E at, Reading<A, E> reading,
                                               Walk<A, E> following, Stop<A, E> stopped) {
        BigDecimal folded = foldedNumber(p, at, reading, following);
        if (folded != null) {
            return new Outcome.Composed<>(LinearForm.constant(ExactRatio.of(folded)));
        }
        LinearForm<A> leaf = reading.leafOf(p, at, stopped.at);
        if (leaf != null) {
            return new Outcome.Composed<>(leaf);
        }
        return stopped.at != null ? stopped.at
                : new Outcome.StoppedAt<>(p, at, new Halt.NoRule<>());
    }

    /**
     * {@code e} as the count it writes on a carrier that counts, or null where it writes none.
     *
     * <p><b>A literal on a counted carrier is a constant of this arithmetic.</b> Which counts a
     * value of a type stands on is the carrier's one answer, and a date written out stands on a day
     * as surely as a number written out stands on itself. Read as an arm per scalar, a name would
     * carry what the value that name stands for does not — so substituting a concrete value into a
     * proposition would take its proof away, which is an answer about how a model is spelled.
     *
     * <p><b>Nothing about any carrier is read here.</b> What a written value counts as is
     * {@link Carrier#literalOf}'s, which is where every reader of a written value asks it and where
     * a newtype's construction around one is taken off. Answered here instead, this walk would hold
     * a second account of what a date is written as.
     *
     * <p>A carrier that writes no constant has none to be: a string is ordered and stands no
     * measurable distance from another, and a case names which case a value is. Both are the
     * carrier's own answers ({@link Carrier#writesAConstant}) and not cases here.
     *
     * <p>Null where the carrier writes no literal at this expression, and the walk goes on to read
     * it as arithmetic or as a leaf. Treated as "not affine" instead, an expression a carrier does
     * not recognise would stop a reading the grammar below can still take apart.
     */
    private static <A, E> LinearForm<A> literal(Core e, E at, Reading<A, E> reading) {
        Carrier carrier =
                Carrier.ofValue(e.type(), reading.declarations());
        if (carrier == null || !carrier.writesAConstant()) {
            return null;
        }
        // The expression as this walk stands at it: a name in front of it is read by this walk,
        // once, and what the carrier takes apart is followed where the expression was written.
        Place place = carrier.literalOf(new ValueStanding.Standing<>(e, at, reading),
                reading.symbols());
        return place == null ? null : LinearForm.constant(Count.number(place).exactly());
    }

    /**
     * {@code call} read as {@code says}, a form of the values it was given — what the case of its
     * operation's definition a reading is on answers — or null where one of those values does not
     * compose. A stop is recorded at the call, for the reason {@link #answered} gives.
     */
    private static <A, E> LinearForm<A> overTheValues(Core call, LinearForm<Core> says, E at,
                                                      Reading<A, E> reading, Walk<A, E> following,
                                                      Stop<A, E> stopped) {
        Stop<A, E> inside = new Stop<>();
        LinearForm<A> form = LinearForm.constant(says.constant());
        for (Map.Entry<Core, ExactRatio> each : says.coefs().entrySet()) {
            LinearForm<A> value = formOf(each.getKey(), at, reading, following, inside);
            if (value == null) {
                return halted(call, at, new Halt.AnArgumentStopped<>(inside.at), stopped);
            }
            LinearForm<A> before = form;
            switch (value.times(each.getValue()).flatMap(before::plus)) {
                case ExactAnswer.Held<LinearForm<A>>(LinearForm<A> held) -> form = held;
                case ExactAnswer.Unheld<LinearForm<A>>(UnheldNumber why) -> {
                    return halted(call, at, new Halt.NotHeld<>(why), stopped);
                }
            }
        }
        return form;
    }

    /**
     * {@code call} read as {@code says}, the form of its arguments the library says it answers,
     * or null where one of the arguments it is written over does not compose.
     *
     * <p>Over what each argument is counted as, which is the form that argument itself reads as
     * here. So a shift of a position by a written number and a shift of one position by another are
     * one rule with two readings, and neither is a case anybody wrote.
     */
    private static <A, E> LinearForm<A> answered(Core call, LinearForm<DeclaredArgument> says,
                                                 E at, Reading<A, E> reading,
                                                 Walk<A, E> following,
                                                 Stop<A, E> stopped) {
        java.util.List<Core> args = Terms.argsOf(call);
        // The expansion's own stops, kept off the walk's. What is inside a declared form is not
        // what an author wrote: the arguments stand where they stand because the library says the
        // operation answers this much of them, and a reader that cannot carry one of them has not
        // met an expression an author would change — it has met this call.
        Stop<A, E> inside = new Stop<>();
        LinearForm<A> form = LinearForm.constant(says.constant());
        // Walked left to right over the call's arguments. A declared form holds which arguments the
        // operation answers over and says nothing about which of them was written first, and where
        // two of them cannot be carried it is the one the walk meets first that the stop is
        // recorded against — so the walk is taken off the call rather than off the form.
        for (Map.Entry<DeclaredArgument, ExactRatio> each : inArgumentOrder(says, call)) {
            // The call here may be the runnable tree's and not a kept one, so its argument count
            // is checked here rather than by a kept call's own constructor.
            int position = CallArguments.positionOf(each.getKey(), Terms.operationOf(call));
            if (position < 0 || position >= args.size()) {
                return halted(call, at, new Halt.NoRule<>(), stopped);
            }
            LinearForm<A> argument = formOf(args.get(position), at, reading, following, inside);
            // Recorded at the call and not at what was found inside it. A stop is reported at the
            // most particular expression with no rule here, which is what an author would change,
            // and inside a form the library declares there is no such expression: the author wrote
            // the call. Reported from within, a rule over what `Date.daysBetween` answers would be
            // a rule about the field the expansion reached, which the model does not state. Why it
            // stopped is the argument's.
            if (argument == null) {
                return halted(call, at, new Halt.AnArgumentStopped<>(inside.at), stopped);
            }
            LinearForm<A> before = form;
            switch (argument.times(each.getValue()).flatMap(before::plus)) {
                case ExactAnswer.Held<LinearForm<A>>(LinearForm<A> held) -> form = held;
                // A number of the declared form, worked out exactly, has no representation here.
                case ExactAnswer.Unheld<LinearForm<A>>(UnheldNumber why) -> {
                    return halted(call, at, new Halt.NotHeld<>(why), stopped);
                }
            }
        }
        return form;
    }

    /**
     * What a declared form weighs, in the order the call writes those arguments down.
     *
     * <p>An argument the operation does not declare sorts last, where the walk meets it and stops
     * at the call: what is not the operation's is not put in front of what is.
     */
    private static List<Map.Entry<DeclaredArgument, ExactRatio>> inArgumentOrder(
            LinearForm<DeclaredArgument> says, Core call) {
        ValueName operation = Terms.operationOf(call);
        return says.coefs().entrySet().stream()
                .sorted(Comparator.comparingInt(each -> {
                    int position = CallArguments.positionOf(each.getKey(), operation);
                    return position < 0 ? Integer.MAX_VALUE : position;
                }))
                .toList();
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
    private static LinearForm<DeclaredArgument> formSaidOf(Core e) {
        souther.compiler.types.ValueName operation = Terms.operationOf(e);
        return operation == null ? null : DischargeRules.answersAFormOf(operation);
    }

    private AffineForms() {}
}
