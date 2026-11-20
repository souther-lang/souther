package souther.compiler.inputs;

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;

/**
 * What shows that a run stops in a rule: the operation, as written, and a value of the input that
 * exists, gets to it with nothing before it ending the run, and works it out past its ends — the
 * whole number at each place of the input that value is asked to hold, and anything at the rest.
 *
 * @param operation the operation the run stops in, as written
 * @param at        the number at each place the value is asked to hold, in the order the input
 *                  declares its places; none where the operation comes to past its ends whatever
 *                  the input holds
 */
public record AStopShown(String operation, List<NumberAt> at) {

    public AStopShown {
        Objects.requireNonNull(operation, "a stop is shown in some operation");
        at = List.copyOf(at);
    }

    /** The whole number {@code number} at the place {@code place} of the input. */
    public record NumberAt(TermPath place, BigInteger number) {

        public NumberAt {
            Objects.requireNonNull(place, "a number is at some place of the input");
            Objects.requireNonNull(number, "a place holds some number");
        }
    }
}
