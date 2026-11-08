package souther.compiler.inputs;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.numeric.LinearForm;

import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The totals of one input's containers, as the input names them: which term a total a rule wrote
 * is, and what a total of a form of each element's places comes to as the totals of those places.
 *
 * <p>Both made by the one maker of these terms ({@link InputNumber}), so a total a rule speaks of
 * and the same total a body reads are one term, and the totals of a form and of its places are
 * related by how they were made. Handed to the reading of the input's rules
 * ({@link ReadQuantities}), which has no input of its own to make terms with.
 *
 * <p>What each total comes to is a function of the term and of this input, asked again of every
 * term put on the rules, so it is kept once per term — by this reading of the input, which is
 * what it is a function of, and by nothing it is handed to.
 */
final class TotalsOfTheInput {

    /** Where the totals are made; null where the input was read without the rules. */
    private final InputDomain inputs;
    private final RuleReadingSource source;
    private final Map<NumericTerm, Optional<LinearForm<NumericTerm>>> addedUp =
            new ConcurrentHashMap<>();

    TotalsOfTheInput(InputDomain inputs, RuleReadingSource source) {
        this.inputs = source == null ? null : inputs;
        this.source = source;
    }

    /** The term {@code total} is, or null where none is made ({@link InputNumber#totalOf}). */
    NumericTerm termOf(TotalOfTheElements total) {
        return inputs == null ? null : InputNumber.totalOf(total, inputs, source);
    }

    /** What {@code term} comes to as the totals of its places, or null where it is no total of
     *  a form of them ({@link InputNumber#whatItAddsUp}). */
    LinearForm<NumericTerm> whatItAddsUp(NumericTerm term) {
        if (inputs == null || !(term instanceof NumericTerm.TakenOver)) {
            return null;
        }
        return addedUp.computeIfAbsent(term, each ->
                Optional.ofNullable(InputNumber.whatItAddsUp(each, inputs, source))).orElse(null);
    }
}
