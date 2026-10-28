package souther.compiler.inputs;

import java.math.BigInteger;
import java.util.List;

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
     * @param form     the numbers weighed and a constant, as an author would write them
     * @param least    the least value the form takes there, or null where nothing bounds it below
     * @param greatest the greatest, or null where nothing bounds it above
     */
    public record Within(String form, BigInteger least, BigInteger greatest) {

        public Within {
            if (form == null || (least == null && greatest == null)
                    || (least != null && greatest != null && least.compareTo(greatest) > 0)) {
                throw new IllegalArgumentException("a form held to some end, and to values");
            }
        }
    }
}
