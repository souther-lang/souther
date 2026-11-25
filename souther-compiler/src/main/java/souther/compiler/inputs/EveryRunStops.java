package souther.compiler.inputs;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.math.BigInteger;
import java.util.List;
import java.util.Optional;

/**
 * Where every run getting to a rule stops in one operation the rule is read through: the rows at
 * which what the operation works out is past what its type holds, and every operation a run may
 * work out before it is within its type.
 *
 * <p>A proof about those rows and not a class of them. A run of {@code x + 1 == y} at the
 * greatest whole number stops in {@code x + 1} before the comparison answers, so the rule is
 * neither true nor false there and no row there is a witness for either side; nor is the value one
 * no row holds, since a row may hold it and stop. What is left open is nothing, so a measure is
 * not held open by it.
 *
 * <p>Said of rows over several positions where the operation is over several: {@code x + z}
 * stops where the two together are past the type, which no value of either alone says. And an
 * operation is said to be the one a run stops in only where every operation a run may work out
 * before it gets past: {@code (x + 1) + 1} stops in {@code x + 2} where {@code x + 1} is within the
 * type, and at the greatest {@code x} in {@code x + 1}, which comes first.
 *
 * <p>Said of the rows that get to the comparison. A row the ways before it keep away from these
 * never works the operation out, and nothing here is said of it.
 *
 * @param operation the operation, written as the numbers it is over weighed and a constant
 * @param where     the rows, as forms each of which lies between two ends: every row meeting all
 *                  of them stops in the operation
 */
public record EveryRunStops(String operation, List<Within> where) {

    public EveryRunStops {
        if (operation == null || where == null || where.isEmpty()) {
            throw new IllegalArgumentException("every run stops at some rows, in some operation");
        }
        where = List.copyOf(where);
    }

    /**
     * A form over numbers of the input, between two ends.
     *
     * <p>The form as the numbers it weighs, and written for an author only where it is said
     * ({@link #written}): a reader that asks whether a row is among these weighs the row's numbers,
     * and a form held as its words would leave it to read them back.
     *
     * @param form     the numbers of the input weighed, each read from one place, and no constant
     * @param least    the least value the form takes there, or null where nothing bounds it below
     * @param greatest the greatest, or null where nothing bounds it above
     */
    public record Within(LinearForm<NumericTerm> form, BigInteger least, BigInteger greatest) {

        public Within {
            if (form == null || (least == null && greatest == null)
                    || (least != null && greatest != null && least.compareTo(greatest) > 0)) {
                throw new IllegalArgumentException("a form held to some end, and to values");
            }
            if (form.coefs().isEmpty() || !form.constant().isZero() || !form.coefs().keySet()
                    .stream().allMatch(NumericTerm.FromOnePosition.class::isInstance)) {
                throw new IllegalArgumentException("a form weighs numbers of the input, each read"
                        + " from one place, and no constant: " + form);
            }
        }

        /** The form as an author would write it. */
        public String written() {
            return form.asAnAuthorWritesIt();
        }

        /** The one number the form is, where it is one number unweighed; none where it is a form
         *  of several. */
        public Optional<NumericTerm.FromOnePosition> alone() {
            return form.coefs().size() == 1
                    && form.coefs().values().iterator().next().equals(ExactRatio.ONE)
                    ? Optional.of((NumericTerm.FromOnePosition) form.coefs().keySet().iterator()
                            .next())
                    : Optional.empty();
        }
    }
}
