package souther.compiler.partition;

import java.math.BigInteger;

/**
 * The whole numbers that leave one remainder by one divisor, and what two such classes have in
 * common.
 *
 * <p>Two classes either share a class of their own, modulo the least common multiple of the two
 * divisors, or share nothing: they share nothing exactly where the two residues differ by something
 * the greatest common divisor does not divide. So what several remainders of one place ask for is
 * answered by arithmetic and not by stepping through the product of the divisors, which is as wide as
 * the figure of steps a search is allowed and a walk that ends there has found out nothing.
 */
record Congruences(BigInteger residue, BigInteger modulus) {

    Congruences {
        if (modulus.signum() <= 0) {
            throw new IllegalArgumentException("a class is of a divisor above nought: " + modulus);
        }
        residue = residue.mod(modulus);
    }

    /** The numbers both classes hold, or null where there are none. */
    Congruences meet(Congruences other) {
        BigInteger gcd = modulus.gcd(other.modulus);
        BigInteger apart = other.residue.subtract(residue);
        if (apart.mod(gcd).signum() != 0) {
            return null;
        }
        BigInteger reducedOther = other.modulus.divide(gcd);
        BigInteger reducedThis = modulus.divide(gcd);
        BigInteger steps = reducedOther.equals(BigInteger.ONE) ? BigInteger.ZERO
                : apart.divide(gcd).multiply(reducedThis.modInverse(reducedOther))
                        .mod(reducedOther);
        BigInteger lcm = modulus.multiply(reducedOther);
        return new Congruences(residue.add(modulus.multiply(steps)), lcm);
    }

    /** The least number of the class that is at or above {@code floor}. */
    BigInteger leastAtOrAbove(BigInteger floor) {
        return floor.add(residue.subtract(floor).mod(modulus));
    }

    /** The greatest number of the class that is at or below {@code ceiling}. */
    BigInteger greatestAtOrBelow(BigInteger ceiling) {
        return ceiling.subtract(ceiling.subtract(residue).mod(modulus));
    }
}
