package souther.compiler.inputs;

import java.math.BigInteger;

/**
 * A run of the values at one position at which every run getting to a rule stops in an operation
 * the rule is read through: what the operation works out is past what its type holds, whatever the
 * other numbers it is over hold there.
 *
 * <p>A proof about the values and not a class of them. A run of {@code x + 1 == y} at the greatest
 * whole number stops in {@code x + 1} before the comparison answers, so the rule is neither true
 * nor false there and no row there is a witness for either side; nor is the value one no row
 * holds, since a row may hold it and stop. What is left open is nothing, so a measure is not held
 * open by it.
 *
 * <p>Said of the operation the comparison was read through, and so of the rows that get to the
 * comparison. A row the ways before it keep away from these values never works the operation out,
 * and nothing here is said of it.
 *
 * @param at        the position
 * @param from      the least value of the run
 * @param to        the greatest value of the run
 * @param operation the operation, written as the numbers it is over weighed and a constant
 */
public record EveryRunStops(FilingCoordinate at, BigInteger from, BigInteger to,
                            String operation) {

    public EveryRunStops {
        if (at == null || from == null || to == null || operation == null
                || from.compareTo(to) > 0) {
            throw new IllegalArgumentException("every run stops at some values of a position, in"
                    + " some operation");
        }
    }
}
