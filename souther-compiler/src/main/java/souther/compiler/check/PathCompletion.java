package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.reach.WhatMayStopARun;
import souther.compiler.semantics.NumericResult;
import souther.compiler.semantics.WhereAnOperatorAnswers;
import souther.compiler.core.Core;
import souther.compiler.types.BinOp;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

/**
 * Whether one evaluation can answer, under what is known where it stands.
 *
 * <p>The same question {@link souther.compiler.coverage.NormalReturn} answers without a path, asked
 * under one. That one reads the tree: an {@code unreachable} answers no value and so does anything
 * that evaluates one on its way, which is true of every run and needs nothing but the tree. This one
 * adds what a run reaching here has established — the operands of a primitive lie where the guards
 * left them, and the operation is defined on some of those and not on others.
 *
 * <p>They agree where the tree is what says it, and this says it too: an {@code unreachable} is
 * answered here as well, so a caller acting on this is not left needing the other. What this does
 * not do is compose. {@code NormalReturn} answers about a whole expression by reading everything
 * under it; this answers about the one evaluation it is handed, and the walk carries the answer
 * forward, which reaches the same conclusion for everything the walk evaluates in order and stops at
 * a region it does not carry facts out of. Under-reading, in the direction everything here
 * under-reads.
 *
 * <p><b>Asked in two steps, because an operation answering no number is not an operation answering
 * nothing.</b> What a recipe says is about the number the operation computes
 * ({@link DerivedNumericFacts.Says}); an operation that answers a union comes back as its other case
 * without computing one, and an arm is reached there. So the recipe is asked first and the other
 * cases after it, and only an operation with no case left to come back as is one no run leaves.
 *
 * <p>Both steps read what already knows. The arithmetic and what a value's kind of number holds are
 * the recipes' ({@link DerivedNumericFacts}); which case comes back and under what condition is the
 * table's ({@link NumericResult.TheOtherCaseWhen}, through {@link TheOtherCase}); and what a
 * condition rules out is {@link Predicates}'. Nothing about a primitive's own domain is written down
 * here, which is what keeps this from being a second place each operation has to be described in.
 *
 * <p>Under-reading in every direction. An operation this cannot name, a recipe with nothing to fire
 * on, an operand nothing bounds, a case this cannot show is unreachable — each answers
 * {@link Completion#MAY}, and what is asked of an evaluation whose definedness nothing settles stays
 * what it was.
 */
final class PathCompletion {

    private final Terms terms;
    private final Predicates predicates;

    PathCompletion(Terms terms, Predicates predicates) {
        this.terms = terms;
        this.predicates = predicates;
    }

    /**
     * What becomes of a run that has reached {@code e} with everything it is computed from answered.
     *
     * @param k what holds there, which is before {@code e}'s own answer says anything — asking it
     *          after would be asking whether an evaluation answers under the assumption that it did
     */
    Completion of(Core e, Known k, Denotations at) {
        return of(e, k, answersNowhere(operated(e, at), k), at);
    }

    /**
     * The same, told whether nothing {@code k} leaves is where {@code e}'s operator answers
     * ({@link WhereAnOperatorAnswers}).
     */
    private Completion of(Core e, Known k, boolean answersNowhere, Denotations at) {
        if (k.reachesNothing()) {
            // Nothing stands here, so there is no run to say anything about. Answered as the
            // weaker of the two, since a state that holds nothing proves whatever it is asked.
            return Completion.MAY;
        }
        if (e instanceof Core.Unreachable said) {
            // Written down rather than worked out, and it is the model that wrote it. Nothing about
            // the path enters into it.
            return new Completion.CannotComplete(
                    new Completion.NoCompletionProof.TheModelSaysNothingArrives(said));
        }
        // Read before the recipes: what the operator asks of its operands is the language's, and
        // a recipe says the number it computes, which is a second and narrower question.
        if (answersNowhere) {
            return new Completion.CannotComplete(new Completion.NoCompletionProof.NotHeld(e));
        }
        Core called = operationAt(e);
        if (called == null) {
            return Completion.MAY;
        }
        // The number the operation computes, which is its own value where it answers one and what
        // one of its cases carries where it answers a union.
        souther.compiler.types.Type carried = TheOtherCase.theCaseItAnswersIn(called);
        FactSubject answer = carried == null ? terms.atomOf(called, at)
                : terms.atomOfTheCaseCarrying(called, carried, at);
        if (answer == null) {
            return Completion.MAY;
        }
        if (!(DerivedNumericFacts.saysOf(answer, k.numbers(), terms)
                instanceof DerivedNumericFacts.Says.NoValueCameOfIt)) {
            return Completion.MAY;
        }
        // The number is one no run computes. Whether the operation answers all the same is what its
        // other case decides: `Int.truncatingDivide` comes back as `DivisionByZero` where the divisor is zero,
        // and a run that takes that arm has carried on. So this is the operation answering nothing
        // only where nothing here can come back as anything else.
        Core otherwise = TheOtherCase.conditionAt(called);
        if (otherwise != null
                && !predicates.assumeCond(otherwise, k, at, true).known().reachesNothing()) {
            return Completion.MAY;
        }
        return new Completion.CannotComplete(
                new Completion.NoCompletionProof.NoValue(called, answer));
    }

    /**
     * What holds once a run that reached {@code e} with everything it is computed from answered has
     * got past it: nothing, where {@code e} answers nothing ({@link #of}), and otherwise {@code k}
     * with what its operator answering asks of the operands taken in.
     *
     * <p>What a walk asking where a run arrives carries on past an evaluation with. {@code a == MAX}
     * and then {@code a + 1} leaves nothing; {@code a >= MAX - 1} and then {@code a + 1} leaves
     * {@code a == MAX - 1}, which is what every run past the sum holds.
     *
     * <p>The invariant check asks {@link #of} and carries nothing more on. What it judges a
     * construction against is read off what the path says of each value, and an end on every value
     * a sum was worked out of says something of each of them — so every product over them would be
     * derived at every construction, which is the work that check is held to doing only for what a
     * construction is about. What it leaves out is a fact, and leaving one out decides nothing it
     * would not otherwise decide.
     *
     * <p>And what, on the way to a run past it, may have stopped a run for what nothing here says:
     * {@code mayStop}, with {@code e} itself where where it answers is not all read here
     * ({@link #readsWhereItAnswers}). Nothing is added where no run gets past, since a place
     * nothing arrives at is not one a run may have stopped on the way to.
     *
     * @param k       what holds before {@code e} answers, as for {@link #of}
     * @param mayStop what may have stopped a run on the way to {@code e}
     */
    Past past(Core e, Known k, Denotations at, List<WhatMayStopARun> mayStop) {
        Operated operated = operated(e, at);
        Known answered = answering(operated, k);
        if (of(e, k, answered.reachesNothing(), at) instanceof Completion.CannotComplete) {
            return new Past(k.reachingNothing(), mayStop);
        }
        WhatMayStopARun stopping = whatStops(operated.e());
        if (mayStop.contains(stopping) || readsWhereItAnswers(operated, k, at)) {
            return new Past(answered, mayStop);
        }
        List<WhatMayStopARun> more = new ArrayList<>(mayStop);
        more.add(stopping);
        return new Past(answered, List.copyOf(more));
    }

    /**
     * What a run past an evaluation holds, and what on the way there may have stopped a run for
     * what nothing here says.
     */
    record Past(Known known, List<WhatMayStopARun> mayStop) {}

    /** Which kind of thing {@code e} is, as one that may stop a run. */
    private static WhatMayStopARun whatStops(Core e) {
        return switch (e) {
            case Core.Binary _, Core.Neg _ -> new WhatMayStopARun.AnOperator();
            case Core.Construct _ -> new WhatMayStopARun.AConstruction();
            default -> new WhatMayStopARun.ACall();
        };
    }

    /**
     * The operator {@code e} is and where it answers, with the form its region is said over —
     * read once for every question asked of the evaluation.
     *
     * @param e     the evaluation, any standing set aside
     * @param where where its operator answers, or null where it is no operator
     * @param form  what {@code where} is said over, where the arithmetic composes it: the value
     *              itself where it answers on a run of exact values, the divisor where it answers
     *              on a divisor that is not nought, and null otherwise
     */
    private record Operated(Core e, WhereAnOperatorAnswers where, LinearForm<FactSubject> form) {}

    private Operated operated(Core standing, Denotations at) {
        Core e = Core.withoutStanding(standing);
        WhereAnOperatorAnswers where = whereItAnswers(e);
        LinearForm<FactSubject> form = switch (where) {
            case WhereAnOperatorAnswers.WhereItsExactValueIsHeld _ ->
                    terms.affineOf(standing, at);
            case WhereAnOperatorAnswers.WhereTheDivisorIsNotNought _ ->
                    e instanceof Core.Binary quotient ? terms.affineOf(quotient.right(), at)
                            : null;
            case null, default -> null;
        };
        return new Operated(e, where, form);
    }

    /** Where the operator {@code e} is answers, or null where {@code e} is no operator. */
    private static WhereAnOperatorAnswers whereItAnswers(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.Binary binary -> WhereAnOperatorAnswers.ofAnOperator(binary.op(),
                    binary.type(), List.of(binary.left().type(), binary.right().type()));
            case Core.Neg neg -> WhereAnOperatorAnswers.ofANegation(neg.type());
            default -> null;
        };
    }

    /**
     * Whether where a run that reached the evaluation gets past it is read here, under {@code k}:
     * every operand it answers on is one {@link #past} keeps, and every one it does not is one past
     * leaves out.
     *
     * <p>Not whether it answers. A sum over two values held to a hundred answers everywhere they
     * are held and is read; a sum over values nothing holds answers where it fits an {@code Int},
     * which is what past takes in, and is read; a product of two values nothing holds answers where
     * their product fits, which no form here says, and is not. A node that is no operator is read
     * where it ends no run ({@link WhatARunMayEndFor}) and not read anywhere else: a call whose
     * kernel may stop, a behavior whose body is not this one, a construction whose rule may refuse.
     *
     * <p>What a reader holding a run that got to a place past {@code e} cannot have is a showing
     * that some run gets there, where this answers false: the rows past {@code e} that
     * {@link #past} keeps include ones that stop at it.
     */
    private boolean readsWhereItAnswers(Operated operated, Known k, Denotations at) {
        if (k.reachesNothing()) {
            return true;
        }
        Core e = operated.e();
        if (operated.where() == null) {
            return WhatARunMayEndFor.itself(e).endsNone();
        }
        return switch (operated.where()) {
            case WhereAnOperatorAnswers.Everywhere _ -> true;
            case WhereAnOperatorAnswers.WhereItsExactValueIsHeld(var least, var greatest) ->
                    (e instanceof Core.Binary product && product.op() == BinOp.MUL)
                            ? heldWherever(product, least, greatest, k, at)
                            : operated.form() != null;
            case WhereAnOperatorAnswers.WhereTheDivisorIsNotNought _ -> operated.form() != null;
            case WhereAnOperatorAnswers.NotStated _ -> false;
        };
    }

    /**
     * Whether {@code product} comes to a number from {@code least} to {@code greatest} wherever
     * {@code k} holds: a scalar multiple is a form, read by {@link #past} as any form is, and a
     * product of two values is read where the ends each is held to keep every product inside.
     */
    private boolean heldWherever(Core.Binary product, BigInteger least, BigInteger greatest,
                                 Known k, Denotations at) {
        LinearForm<FactSubject> left = terms.affineOf(product.left(), at);
        LinearForm<FactSubject> right = terms.affineOf(product.right(), at);
        if (left == null || right == null) {
            return false;
        }
        if (left.coefs().isEmpty() || right.coefs().isEmpty()) {
            return true;
        }
        NumericDomain.Bounds of = k.numbers().boundsOf(left);
        NumericDomain.Bounds by = k.numbers().boundsOf(right);
        List<ExactRatio> ends = new ArrayList<>();
        for (Endpoint one : new Endpoint[] {of.min(), of.max()}) {
            for (Endpoint other : new Endpoint[] {by.min(), by.max()}) {
                if (one == null || other == null || !(one.at() instanceof Count a)
                        || !(other.at() instanceof Count b)
                        || !(a.exactly().times(b.exactly())
                                instanceof ExactAnswer.Held<ExactRatio>(var corner))) {
                    return false;
                }
                ends.add(corner);
            }
        }
        return ends.stream().allMatch(corner -> corner.compareTo(ExactRatio.of(least)) >= 0
                && corner.compareTo(ExactRatio.of(greatest)) <= 0);
    }

    /**
     * {@code k} with the operands of {@code e} where its operator answers
     * ({@link WhereAnOperatorAnswers}), as far as the numbers here can say it.
     *
     * <p>Only where what its region is said over is a form over what this reads: the value of a
     * sum, a difference, a scalar multiple or a negation, and the divisor of a quotient. A product
     * of two values is one atom here, and an end on that atom says nothing of either factor, though
     * it is no less true. What is not said here is left as it was, which over-reads where a run
     * gets past and never under-reads it.
     */
    private Known answering(Operated operated, Known k) {
        return taking(asked(operated, k), k);
    }

    /** {@code k} with {@code asked} taken in as holding on the path. */
    private Known taking(List<NumericConstraint> asked, Known k) {
        Known out = k;
        for (NumericConstraint one : asked) {
            out = out.taking(one.form(), one.rel(), Known.Held.ON_THE_PATH,
                    terms.kindsOf(one.form()));
        }
        return out;
    }

    /**
     * What {@link #answering} takes in, as relations: the operands where the operator answers, less
     * what {@code k} already holds. Each is checked against {@code k} and not against the ones
     * before it, which are the same operator's other end.
     */
    private List<NumericConstraint> asked(Operated operated, Known k) {
        LinearForm<FactSubject> form = operated.form();
        if (form == null) {
            return List.of();
        }
        // What holds already is not taken again, so a run past an operator that answers wherever
        // it is reached holds what it held — and the same state.
        if (operated.where() instanceof WhereAnOperatorAnswers.WhereTheDivisorIsNotNought) {
            return k.numbers().entails(form, Rel.NE) ? List.of()
                    : List.of(new NumericConstraint(form, Rel.NE));
        }
        if (!(operated.where() instanceof WhereAnOperatorAnswers.WhereItsExactValueIsHeld(
                BigInteger least, BigInteger greatest))) {
            return List.of();
        }
        List<NumericConstraint> out = new ArrayList<>();
        if (form.minus(LinearForm.constant(ExactRatio.of(greatest)))
                instanceof ExactAnswer.Held<LinearForm<FactSubject>>(var above)
                && !k.numbers().entails(above, Rel.LE)) {
            out.add(new NumericConstraint(above, Rel.LE));
        }
        if (form.minus(LinearForm.constant(ExactRatio.of(least)))
                instanceof ExactAnswer.Held<LinearForm<FactSubject>>(var below)
                && !k.numbers().entails(below, Rel.GE)) {
            out.add(new NumericConstraint(below, Rel.GE));
        }
        return out;
    }

    /**
     * What a run needs of the numbers to work {@code leaf} out, one part of a clause of no
     * connective, wherever it is reached.
     *
     * <p>The forms a part comes to are the part over the whole numbers, and a run works it out over
     * the numbers a type holds. Under {@code value + M > 0} the sum answers where {@code value} is
     * not above nought, and the form {@code value > -M} says nothing of it. Each operator is read
     * where it is written and not where it is composed into: {@code value + M - M >= 1} comes to
     * {@code value >= 1}, and the run stops at the sum all the same.
     *
     * <p>What an operator asks is taken in for the operators after it, so that one asked twice is
     * asked once. A node whose children are not all worked out whenever it is — the arms of an
     * {@code if}, the right of a connective inside an operand — is not read into, and says so if an
     * operator under it may stop a run: leaving one out is the weaker answer, and not saying it
     * would make it the stronger.
     *
     * @param k what holds where the part is worked out, which an operator's ask is not repeated of
     */
    WorkingOutNeeds workedOut(Core leaf, Known k, Denotations at) {
        List<NumericConstraint> asked = new ArrayList<>();
        boolean[] read = {true};
        workedOut(leaf, k, at, asked, read);
        return new WorkingOutNeeds(asked, read[0]);
    }

    /** The same, adding to {@code asked} and clearing {@code read[0]}, and answering what holds past
     *  {@code e}. */
    private Known workedOut(Core e, Known k, Denotations at, List<NumericConstraint> asked,
                            boolean[] read) {
        Core bare = Core.withoutStanding(e);
        Known past = k;
        switch (bare) {
            case Core.Binary binary when binary.op() == BinOp.AND || binary.op() == BinOp.OR -> {
                // The left is worked out first, and the right only on the runs the left lets
                // through.
                past = workedOut(binary.left(), past, at, asked, read);
                read[0] &= endsNone(binary.right());
                return past;
            }
            case Core.Binary binary -> {
                past = workedOut(binary.left(), past, at, asked, read);
                past = workedOut(binary.right(), past, at, asked, read);
            }
            case Core.Neg neg -> past = workedOut(neg.operand(), past, at, asked, read);
            case Core.PreservedCall call -> {
                for (Core argument : call.args()) {
                    past = workedOut(argument, past, at, asked, read);
                }
                // What the operation itself ends a run for is the library's to say, and nothing
                // here says on which arguments.
                read[0] &= WhatARunMayEndFor.itself(call).endsNone();
                return past;
            }
            case Core.If branching -> {
                past = workedOut(branching.cond(), past, at, asked, read);
                read[0] &= endsNone(branching.then()) && endsNone(branching.els());
                return past;
            }
            default -> {
                read[0] &= endsNone(bare);
                return past;
            }
        }
        Operated operated = operated(e, at);
        switch (operated.where()) {
            case WhereAnOperatorAnswers.Everywhere _ -> { }
            case WhereAnOperatorAnswers.NotStated _ -> read[0] = false;
            case WhereAnOperatorAnswers.WhereItsExactValueIsHeld(var least, var greatest) -> {
                past = operandsHeld(bare, least, greatest, past, at);
                if (bare instanceof Core.Binary product && product.op() == BinOp.MUL
                        && aProductOfValues(product, at)) {
                    read[0] &= heldWherever(product, least, greatest, past, at);
                } else if (operated.form() == null) {
                    read[0] = false;
                } else {
                    List<NumericConstraint> now = asked(operated, past);
                    asked.addAll(now);
                    past = taking(now, past);
                }
            }
            case WhereAnOperatorAnswers.WhereTheDivisorIsNotNought _ -> {
                if (operated.form() == null) {
                    read[0] = false;
                } else {
                    List<NumericConstraint> now = asked(operated, past);
                    asked.addAll(now);
                    past = taking(now, past);
                }
            }
        }
        return past;
    }

    /**
     * {@code k} with each operand of the operator {@code e} held to the numbers its type holds,
     * from {@code least} to {@code greatest}.
     *
     * <p>An operand is a value of the type the operator takes, so it is there whatever the rules
     * say of it. Without this a sum of two lengths asks that it fit and is told nothing holds that,
     * though neither is above the greatest {@code Int}.
     */
    private Known operandsHeld(Core e, BigInteger least, BigInteger greatest, Known k,
                               Denotations at) {
        List<Core> operands = switch (Core.withoutStanding(e)) {
            case Core.Binary binary -> List.of(binary.left(), binary.right());
            case Core.Neg neg -> List.of(neg.operand());
            default -> List.of();
        };
        Known out = k;
        for (Core operand : operands) {
            LinearForm<FactSubject> form = terms.affineOf(operand, at);
            if (form == null || form.coefs().isEmpty()) {
                continue;
            }
            if (form.minus(LinearForm.constant(ExactRatio.of(greatest)))
                    instanceof ExactAnswer.Held<LinearForm<FactSubject>>(var above)) {
                out = out.taking(above, Rel.LE, Known.Held.ON_THE_PATH, terms.kindsOf(above));
            }
            if (form.minus(LinearForm.constant(ExactRatio.of(least)))
                    instanceof ExactAnswer.Held<LinearForm<FactSubject>>(var below)) {
                out = out.taking(below, Rel.GE, Known.Held.ON_THE_PATH, terms.kindsOf(below));
            }
        }
        return out;
    }

    /** Whether {@code product} multiplies two values, neither of which is a number written. */
    private boolean aProductOfValues(Core.Binary product, Denotations at) {
        LinearForm<FactSubject> left = terms.affineOf(product.left(), at);
        LinearForm<FactSubject> right = terms.affineOf(product.right(), at);
        return left != null && right != null && !left.coefs().isEmpty()
                && !right.coefs().isEmpty();
    }

    /** Whether working {@code e} out, and everything under it, is known to end no run. */
    private static boolean endsNone(Core e) {
        return WhatARunMayEndFor.of(e).endsNone();
    }

    /**
     * Whether {@code k} leaves nothing where {@code e}'s operator answers, asked of what holds
     * rather than of {@link #answering}'s state: a caller asking only whether the evaluation
     * answers keeps nothing taken in, so nothing is built for it.
     */
    private boolean answersNowhere(Operated operated, Known k) {
        LinearForm<FactSubject> form = operated.form();
        if (form == null) {
            return false;
        }
        if (operated.where() instanceof WhereAnOperatorAnswers.WhereTheDivisorIsNotNought) {
            return k.numbers().entails(form, Rel.EQ);
        }
        if (!(operated.where() instanceof WhereAnOperatorAnswers.WhereItsExactValueIsHeld(
                BigInteger least, BigInteger greatest))) {
            return false;
        }
        if (form.minus(LinearForm.constant(ExactRatio.of(greatest)))
                instanceof ExactAnswer.Held<LinearForm<FactSubject>>(var above)
                && k.numbers().entails(above, Rel.GT)) {
            return true;
        }
        return form.minus(LinearForm.constant(ExactRatio.of(least)))
                instanceof ExactAnswer.Held<LinearForm<FactSubject>>(var below)
                && k.numbers().entails(below, Rel.LT);
    }

    /**
     * {@code e} where it is a node whose own value this reading records arithmetic for, and null
     * where it is anything else.
     *
     * <p>Which is a product, a quotient and a library call, and it is those because those are what
     * {@link Terms} records a recipe against — not because they are everything the language calls
     * arithmetic. A sum, a difference and a negation are forms, and where they answer is read off
     * the form ({@link #answering}); no recipe is recorded for any of them, so asking one would name
     * the value for nothing.
     *
     * <p>A name given such a value is not one of them. What a name reads was computed where it was
     * computed, and a run standing at the name has already come back from that — so asking here
     * would put the abort after everything written between the two, and a construction among them is
     * one the program builds.
     */
    private static Core operationAt(Core e) {
        if (e instanceof Core.Binary binary) {
            return binary.op() == BinOp.MUL || binary.op() == BinOp.DIV ? e : null;
        }
        return Terms.operationOf(e) != null ? e : null;
    }
}
