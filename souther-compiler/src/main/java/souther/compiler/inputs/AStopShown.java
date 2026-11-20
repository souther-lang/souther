package souther.compiler.inputs;

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;

/**
 * What showed that a run stops in a rule, as a finding carries it: the operation, as written, and
 * the value of the input the proof rested on — the whole number at each place of the input that
 * value is asked to hold, and anything at the rest.
 *
 * <p>The published account of a proof, and not the proof. The proof is made by the stop
 * assessment of a comparison and by nothing else, once a value is shown to exist, to get to the
 * operation with nothing before it ending the run, and to work the operation out past its ends;
 * this is what that proof is said as. Building one of these shows nothing, and a finding that a run
 * stops is made from the assessment's proofs alone.
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
