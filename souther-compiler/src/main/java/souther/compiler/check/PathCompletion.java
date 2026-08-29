package souther.compiler.check;

import souther.compiler.semantics.NumericResult;
import souther.compiler.core.Core;

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
        // other case decides: `Int.divide` comes back as `DivisionByZero` where the divisor is zero,
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
     * {@code e} where it is a node whose own value this reading records arithmetic for, and null
     * where it is anything else.
     *
     * <p>Which is an operator and a library call, and it is those because those are what
     * {@link Terms} records a recipe against — not because they are everything the language calls
     * arithmetic. Negation is arithmetic and is neither, and nothing is recorded for it; a recipe
     * written for it later belongs here, and until one is there would be nothing here to ask.
     *
     * <p>A name given such a value is not one of them. What a name reads was computed where it was
     * computed, and a run standing at the name has already come back from that — so asking here
     * would put the abort after everything written between the two, and a construction among them is
     * one the program builds.
     */
    private static Core operationAt(Core e) {
        return e instanceof Core.Binary || Terms.operationOf(e) != null ? e : null;
    }
}
