package souther.compiler.inputs;

import java.math.BigInteger;
import java.util.Map;
import java.util.Objects;

/**
 * What shows that a run stops in a rule: the operation, as written, and a value of the input that
 * exists, gets to it with nothing before it ending the run, and works it out past its ends — the
 * whole number at each place of the input that value is asked to hold, and anything at the rest.
 *
 * @param operation the operation the run stops in, as written
 * @param at        the number at each place the value is asked to hold; none where the operation
 *                  comes to past its ends whatever the input holds
 */
public record AStopShown(String operation, Map<TermPath, BigInteger> at) {

    public AStopShown {
        Objects.requireNonNull(operation, "a stop is shown in some operation");
        at = Map.copyOf(at);
    }
}
