package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionBounds;
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
                BigInteger bound = each.rangeLeft().max().wholeAdmitted(false);
                if (bound != null) {
                    most = most == null ? bound : most.min(bound);
                }
            }
        }
        return most;
    }
}
