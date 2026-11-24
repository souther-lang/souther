package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionBounds;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.semantics.TakenAs;

import java.math.BigInteger;

/**
 * The most a value at a place holds, as the rules the place is held to leave it: the code points
 * of a string and the elements of a container are each how many the value holds
 * ({@link TakenAs.HowManyItHolds}), and a rule bounding that number bounds every value there.
 *
 * <p>A ceiling over every value, and no claim that a value holds that many. It holds whether or
 * not the rules are read whole, since every value a place holds is one its rules held of.
 */
final class HowManyAPlaceHolds {

    private HowManyAPlaceHolds() { }

    /** The most a value at {@code at} holds, or null where no rule ends how many it holds. */
    static BigInteger atMost(Position at) {
        BigInteger most = null;
        for (PositionBounds each : at.bounds()) {
            if (each.term() instanceof NumericTerm.TakenOf taken
                    && taken.takenAs() instanceof TakenAs.HowManyItHolds
                    && taken.position().equals(at.path())
                    && each.rangeLeft() != null && each.rangeLeft().max() != null) {
                BigInteger bound = mostUpTo(each.rangeLeft().max());
                if (bound != null) {
                    most = most == null ? bound : most.min(bound);
                }
            }
        }
        return most;
    }

    /** The most a count the end {@code end} lets through can be, or null where it is no count. */
    static BigInteger mostUpTo(Endpoint end) {
        if (!(end.at() instanceof Count count)
                || !(count.exactly().floor() instanceof ExactAnswer.Held<BigInteger>(
                        BigInteger whole))) {
            return null;
        }
        return count.exactly().isWhole() && !end.inclusive() ? whole.subtract(BigInteger.ONE)
                : whole;
    }
}
