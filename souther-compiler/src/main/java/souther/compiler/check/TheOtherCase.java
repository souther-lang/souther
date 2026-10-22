package souther.compiler.check;

import souther.compiler.semantics.NumericResult;
import souther.compiler.core.Core;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

/**
 * The condition a union-answering operation comes back as a case other than its number's under,
 * written as the comparison it is.
 *
 * <p>{@link NumericResult.TheOtherCaseWhen} states it as a relation between an argument and a
 * number, which is what the table can say without knowing how a comparison is read. Turning that
 * into a condition is the one step between the table and every reader of it, and it is here so that
 * there is one such step: an arm asks what taking it settles, and a walk asks whether the other case
 * can come back at all, and two spellings of the same comparison would be two accounts of what
 * {@code DivisionByZero} means.
 *
 * <p>Nothing here decides anything. What the comparison establishes is {@link Predicates}' to say,
 * and what a state does with it belongs to whoever asked.
 */
final class TheOtherCase {

    /**
     * The condition {@code called} answers a case other than its number under, or null where the
     * operation has no other case, is not one this table states a result for, or does not answer its
     * number as a case at all.
     *
     * @param called the call as the naming resolved it ({@link Terms#originating})
     */
    static Core conditionAt(Core called) {
        NumericResult<DeclaredArgument> result = called == null ? null
                : DischargeRules.numericResult(Terms.operationOf(called));
        if (result == null || result.unless() == null
                || !(result.at() instanceof NumericResult.Answered.InTheCaseCarrying)) {
            return null;
        }
        Core argument = Terms.argsOf(called).get(CallArguments.positionOf(
                result.unless().argument(), Terms.operationOf(called)));
        // The number as a source would write it beside the argument, so the condition compares
        // the two as a source-written one would.
        ConstantComparison.WrittenBeside than = ConstantComparison.writtenBeside(argument,
                ExactRatio.of(result.unless().than()));
        return than == null ? null : new Core.Binary(result.unless().op(), argument,
                than.number(), than.reading(), ConstructOccurrence.unwritten(), Type.BOOL,
                argument.pos());
    }

    /** The type the number's case carries, or null where {@code called} answers no number as a
     * case. Asked beside the condition because an arm is told apart by what it names. */
    static Type theCaseItAnswersIn(Core called) {
        NumericResult<DeclaredArgument> result = called == null ? null
                : DischargeRules.numericResult(Terms.operationOf(called));
        return result != null
                && result.at() instanceof NumericResult.Answered.InTheCaseCarrying(Type answersIn)
                ? answersIn : null;
    }

    private TheOtherCase() {}
}
