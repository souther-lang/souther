package souther.compiler.meaning;

import souther.compiler.inputs.Quantities;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.util.Map;

/**
 * Which of the numbers a statement is over are whole numbers on every row.
 *
 * <p>Not something a statement holds: a number of the input is whole where the order it is
 * measured on is ({@link Quantities#countsWhole}), which is the input's to say. So a reader that
 * asks a statement what is one line over whole numbers is handed this by whoever read the input.
 */
@FunctionalInterface
public interface WholeNumbers {

    /** None of them is known to be whole: every number may stand between two whole ones. */
    WholeNumbers NONE = _ -> false;

    /** Whether {@code atom} is a whole number on every row. */
    boolean counts(Quantity atom);

    /** The numbers of the input {@code quantities} measures in whole numbers, and nothing else. */
    static WholeNumbers ofTheInput(Quantities quantities) {
        return atom -> atom instanceof DecisionAtom.OfTheInput(var term, var _)
                && quantities.countsWhole(term);
    }

    /** Whether {@code form} without its constant is a whole number on every row: every atom whole
     *  and weighed by a whole number. */
    default boolean weighsOnlyWholeNumbers(LinearForm<Quantity> form) {
        if (form.coefs().isEmpty()) {
            return false;
        }
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (!each.getValue().isWhole() || !counts(each.getKey())) {
                return false;
            }
        }
        return true;
    }
}
