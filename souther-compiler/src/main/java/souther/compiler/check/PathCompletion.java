package souther.compiler.check;

import souther.compiler.core.Core;

/**
 * Whether one evaluation can answer, under what is known where it stands.
 *
 * <p>The path-sensitive half of a question {@link souther.compiler.coverage.NormalReturn} answers
 * without a path. That one reads the tree: an {@code unreachable} answers no value and so does
 * anything that evaluates one on its way, which is true of every run and is why it needs nothing
 * but the tree. This one is that same question narrowed by what a run reaching here has established
 * — the operands of a primitive lie where the guards left them, and the operation is defined on
 * some of those and not on others. So it can only answer where the wider reading has not, and the
 * two are one question at two strengths rather than two questions.
 *
 * <p><b>Asked in two steps, because an operation answering no number is not an operation answering
 * nothing.</b> What a recipe says is about the number the operation computes
 * ({@link DerivedNumericFacts.Says}); an operation that answers a union comes back as its other case
 * without computing one, and an arm is reached there. So the recipe is asked first and the other
 * cases after it, and only an operation with no case left to come back as is one no run leaves.
 *
 * <p>Both steps read what already knows. The arithmetic and what a value's kind of number holds are
 * the recipes' ({@link DerivedNumericFacts}); which case comes back and under what condition is the
 * table's ({@link DischargeRules.TheOtherCaseWhen}, through {@link TheOtherCase}); and what a
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
            return Completion.MAY;
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
     * {@code e} where it is an operation computing a value, and null where it is anything else.
     *
     * <p>The two spellings the language has for arithmetic, and only those. An operator aborts where
     * it runs out of room and a library call answers a case or aborts, and both are evaluations a
     * run either leaves or does not.
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
