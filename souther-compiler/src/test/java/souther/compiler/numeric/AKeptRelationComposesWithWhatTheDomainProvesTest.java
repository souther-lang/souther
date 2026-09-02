package souther.compiler.numeric;


import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation of neither shape is kept as it was written, and what is kept is a premise and not only
 * something to match a goal against. A goal follows from a kept relation where the difference between
 * the two is one the intervals and differences prove: {@code f <= 0} and {@code g - f <= 0} give
 * {@code g <= 0}.
 *
 * <p>One step, and only one. The difference is closed over the shapes the domain derives in; the kept
 * relations are not closed over each other, so a goal reachable only by adding two of them together is
 * not reached. That bound is what keeps the decidable fragment a stated one rather than whatever a
 * search happened to find.
 */
class AKeptRelationComposesWithWhatTheDomainProvesTest {

    private static final String A = "a";
    private static final String B = "b";
    private static final String C = "c";
    private static final String D = "d";
    private static final String E = "e";

    private static LinearForm<String> atom(String a) {
        return LinearForm.<String>atom(a);
    }

    private static LinearForm<String> num(long n) {
        return LinearForm.<String>constant(BigDecimal.valueOf(n));
    }

    /** {@code a + b - c}, which is of neither shape: three atoms, so it is kept as written. */
    private static LinearForm<String> aPlusBMinus(String c) {
        return atom(A).plus(atom(B)).minus(atom(c));
    }

    private static Map<String, Granularity> dense(String... atoms) {
        Map<String, Granularity> out = new LinkedHashMap<>();
        for (String each : atoms) {
            out.put(each, Granularity.DENSE);
        }
        return out;
    }

    /** {@code a + b <= c} and {@code c <= d} give {@code a + b <= d}. The first is kept as written and
     * the second is a difference; nothing but their sum reaches the goal. */
    @Test
    void aKeptRelationComposesWithADifference() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(aPlusBMinus(C), Rel.LE, dense(A, B, C))
                .assume(atom(C).minus(atom(D)), Rel.LE, dense(C, D));

        assertTrue(d.entails(aPlusBMinus(D), Rel.LE), "a + b <= c and c <= d give a + b <= d");
    }

    /** The same with an interval on the other side: {@code a + b <= c} and {@code c <= 100} give
     * {@code a + b <= 100}. What carries a kept relation onward is not the difference matrix in
     * particular but whatever the domain proves of the residual. */
    @Test
    void aKeptRelationComposesWithAnIntervalBound() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(aPlusBMinus(C), Rel.LE, dense(A, B, C))
                .assume(atom(C).minus(num(100)), Rel.LE, dense(C));

        assertTrue(d.entails(atom(A).plus(atom(B)).minus(num(100)), Rel.LE),
                "a + b <= c and c <= 100 give a + b <= 100");
    }

    /** A strict residual makes the goal strict: {@code a + b <= c} and {@code c < d} give
     * {@code a + b < d}. */
    @Test
    void aStrictResidualCarriesItsStrictnessToTheGoal() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(aPlusBMinus(C), Rel.LE, dense(A, B, C))
                .assume(atom(C).minus(atom(D)), Rel.LT, dense(C, D));

        assertTrue(d.entails(aPlusBMinus(D), Rel.LT), "a + b <= c and c < d give a + b < d");
    }

    /** A strict premise does the same from the other side: {@code a + b < c} and {@code c <= d} give
     * {@code a + b < d}, so the residual is only asked for what the premise did not already give. */
    @Test
    void aStrictKeptRelationLeavesTheResidualNothingToProve() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(aPlusBMinus(C), Rel.LT, dense(A, B, C))
                .assume(atom(C).minus(atom(D)), Rel.LE, dense(C, D));

        assertTrue(d.entails(aPlusBMinus(D), Rel.LT), "a + b < c and c <= d give a + b < d");
    }

    /** Neither side strict proves neither: {@code a + b <= c} and {@code c <= d} leave
     * {@code a + b = d} admitted, so {@code a + b < d} does not follow. */
    @Test
    void twoNonStrictRelationsDoNotProveAStrictGoal() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(aPlusBMinus(C), Rel.LE, dense(A, B, C))
                .assume(atom(C).minus(atom(D)), Rel.LE, dense(C, D));

        assertFalse(d.entails(aPlusBMinus(D), Rel.LT), "a + b = d is admitted, so a + b < d is not");
    }

    /** The kept relations are not closed over each other. {@code a + b <= c} and {@code c <= d + e}
     * would give {@code a + b <= d + e} by adding the two, and both are of neither shape, so the
     * residual of either against the goal is of neither shape too and nothing proves it. */
    @Test
    void twoKeptRelationsAreNotAddedTogether() {
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(aPlusBMinus(C), Rel.LE, dense(A, B, C))
                .assume(atom(C).minus(atom(D)).minus(atom(E)), Rel.LE, dense(C, D, E));

        assertFalse(d.entails(atom(A).plus(atom(B)).minus(atom(D)).minus(atom(E)), Rel.LE),
                "adding two kept relations is outside the fragment this derives in");
    }
}
