package souther.compiler.numeric;

import java.math.BigInteger;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * A form every number of which is a whole number the host writes: its constant and each of its
 * weights, as whole numbers.
 *
 * <p>What arithmetic modulo a divisor works on. Being whole is not enough for that: a whole number
 * whose digits the host holds no place for is whole and has no residue anybody can work out. So a
 * reader that is to do whole-number arithmetic on a form asks for one of these
 * ({@link LinearForm#overWholeNumbers}) and is answered where it can be done, rather than asking
 * whether the numbers are whole and then reading them as though they were written.
 *
 * @param constant what the form comes to where every atom is nought
 * @param weights  what each atom is multiplied by, in the order the form holds them
 */
public record WholeForm<A>(BigInteger constant, Map<A, BigInteger> weights) {

    public WholeForm {
        weights = Collections.unmodifiableMap(new LinkedHashMap<>(weights));
    }

    /** What the form weighs {@code atom} by, nought where it does not weigh it. */
    public BigInteger weightOf(A atom) {
        return weights.getOrDefault(atom, BigInteger.ZERO);
    }

    /** The greatest number dividing every weight, which is the step the values of the form
     *  without its constant come in; nought where it weighs nothing. */
    public BigInteger step() {
        BigInteger step = BigInteger.ZERO;
        for (BigInteger each : weights.values()) {
            step = step.gcd(each);
        }
        return step;
    }
}
