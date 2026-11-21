package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.LinearForm;

import java.util.List;
import java.util.Objects;

/**
 * How a run can make a value it works out come to a number of the input: on any row of the input
 * that meets {@link #holding}, the value is {@link #form}.
 *
 * <p>An equality and nothing more. That some row meets {@code holding} is not said: the numbers
 * the form and the conditions are over have to exist together with what is asked of them
 * ({@link AValueOfTheInput}), which is what makes a stop at an operation over the value a stop some
 * run comes to. Where a value is one of several it may be, none of them is an attainment unless
 * what makes the run take it is among {@code holding}: the range the value is read to come to
 * ({@link WhereAValueComesFrom}) is an upper bound, and says nothing of which row gets which of
 * the numbers in it.
 *
 * @param form    the number the value is, over the numbers of the input
 * @param holding what a row has to meet for the value to be that number, each as a constraint on
 *                the numbers of the input
 */
record Attainment(LinearForm<NumericTerm> form, List<TakenConstraint.Affine> holding) {

    Attainment {
        Objects.requireNonNull(form, "the number a value comes to");
        holding = List.copyOf(holding);
    }

    /** The value is {@code form} on every row. */
    static Attainment always(LinearForm<NumericTerm> form) {
        return new Attainment(form, List.of());
    }
}
