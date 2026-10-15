package souther.compiler.inputs;

import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.NumericDomain;

import java.math.BigDecimal;
import java.math.BigInteger;

/**
 * Where a run of whole numbers reaches once only the numbers of one residue class are left in it.
 *
 * <p>A residue class is not a run, and the region's ends say nothing of the numbers between them.
 * What they can say is the first number of the class the run holds and the last, and that is the run
 * of the class: a number a search names at the lower end is a number of the class, where the lower
 * end of the run itself is a number of it only by luck. The ends are the whole of the answer here
 * and the numbers between them are not asked for, so a class with a hole in the middle of the run is
 * a run all the same.
 *
 * <p>A run with no number of the class in it comes back crossed, which is the run that holds
 * nothing and is how a region says so.
 */
final class ResidueHull {

    private ResidueHull() {
    }

    /** {@code runs} narrowed to the numbers of {@code members}. */
    static NumericDomain.Bounds of(NumericDomain.Bounds runs, Congruences members) {
        BigInteger residue = members.residue();
        BigInteger modulus = members.modulus();
        Endpoint low = runs.min() == null ? null : lowest(runs.min(), residue, modulus);
        Endpoint high = runs.max() == null ? null : highest(runs.max(), residue, modulus);
        // An end the exact arithmetic could not hold stays where it was: a run left as wide as it
        // was is the sound answer with less.
        return new NumericDomain.Bounds(low == null ? runs.min() : low,
                high == null ? runs.max() : high);
    }

    /** The first number at or above {@code end} that leaves the residue, or null where the end
     *  names no whole number this holds. */
    private static Endpoint lowest(Endpoint end, BigInteger residue, BigInteger modulus) {
        if (!(end.at() instanceof Count count)
                || !(count.exactly().ceiling() instanceof ExactAnswer.Held<BigInteger> edge)) {
            return null;
        }
        BigInteger from = !end.inclusive() && count.exactly().isWhole()
                ? edge.value().add(BigInteger.ONE) : edge.value();
        BigInteger first = from.add(residue.subtract(from).mod(modulus));
        return Endpoint.inclusive(new Count(new BigDecimal(first)));
    }

    /** The last number at or below {@code end} that leaves the residue, or null where the end
     *  names no whole number this holds. */
    private static Endpoint highest(Endpoint end, BigInteger residue, BigInteger modulus) {
        if (!(end.at() instanceof Count count)
                || !(count.exactly().floor() instanceof ExactAnswer.Held<BigInteger> edge)) {
            return null;
        }
        BigInteger to = !end.inclusive() && count.exactly().isWhole()
                ? edge.value().subtract(BigInteger.ONE) : edge.value();
        BigInteger last = to.subtract(to.subtract(residue).mod(modulus));
        return Endpoint.inclusive(new Count(new BigDecimal(last)));
    }
}
