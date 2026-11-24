package souther.compiler.meaning;

import java.math.BigInteger;
import java.util.Objects;
import java.util.Optional;

/**
 * How many ways there were of choosing one of the cases a line was said for, counted where taking
 * them apart stopped at their number: every way there is, and how many of them no comparison
 * chosen on the way refutes as numbers.
 *
 * <p>Of the cases one case of the line was said for, and of no others: two such cases of one line
 * are counted each on its own, since ways of choosing in one are no ways in the other and a sum of
 * the two is the number of neither.
 *
 * @param structuralWays            every way of choosing one, as the choices stand
 *                                  ({@link DecidingCase.Cases#structuralWays})
 * @param numericallyConsistentWays how many of them are not refuted as numbers, or that this was
 *                                  not counted ({@link NumericallyConsistentWays})
 * @param walkedWaysAtMost          where the line was cut off though the consistent ways are no
 *                                  more than are taken apart, the ways a walk would come to the end
 *                                  of from every start of the remainders together, no more than
 *                                  that: a way holding at several starts is walked from each, and
 *                                  the consistent ways count it once. It is the cost the line was
 *                                  cut off at, and a bound on it, since no question the walk would
 *                                  ask ends a way sooner in it
 */
public record CaseCount(Ways structuralWays,
                        NumericallyConsistentWays.Counted numericallyConsistentWays,
                        Optional<BigInteger> walkedWaysAtMost) {

    /** Counted where no walk from the starts of the remainders was costed. */
    public CaseCount(Ways structuralWays,
                     NumericallyConsistentWays.Counted numericallyConsistentWays) {
        this(structuralWays, numericallyConsistentWays, Optional.empty());
    }

    /**
     * Past how many ways a count is not written out: two to the power of a thousand and
     * twenty-four, longer than any reader reads and as long again to work out.
     */
    public static final BigInteger WAYS_A_COUNT_IS_HELD_TO = BigInteger.TWO.pow(1024);

    public CaseCount {
        Objects.requireNonNull(structuralWays, "cases are some number of ways");
        Objects.requireNonNull(numericallyConsistentWays, "the consistent ways were counted or not");
        Objects.requireNonNull(walkedWaysAtMost, "a walk was costed or it was not");
        if (walkedWaysAtMost.isPresent() && walkedWaysAtMost.get().signum() < 0) {
            throw new IllegalArgumentException("a count of ways is some number of them");
        }
    }

    /** How many ways, as far as a count is held. */
    public sealed interface Ways {

        /** Exactly {@code ways}. */
        record Exactly(BigInteger ways) implements Ways {

            public Exactly {
                if (ways == null || ways.signum() < 0) {
                    throw new IllegalArgumentException("a count of ways is some number of them");
                }
            }
        }

        /** More than {@code ways}, which is {@link #WAYS_A_COUNT_IS_HELD_TO}. */
        record MoreThan(BigInteger ways) implements Ways {

            public MoreThan {
                Objects.requireNonNull(ways, "more than some number");
            }
        }

        /** {@code counted}, where it was counted to {@link #WAYS_A_COUNT_IS_HELD_TO} and one past
         *  it stands for more. */
        static Ways held(BigInteger counted) {
            return counted.compareTo(WAYS_A_COUNT_IS_HELD_TO) > 0
                    ? new MoreThan(WAYS_A_COUNT_IS_HELD_TO) : new Exactly(counted);
        }
    }

    /** {@code cases} counted both ways. */
    public static CaseCount of(DecidingCase.Cases cases) {
        return of(cases, NumericallyConsistentWays.of(cases));
    }

    /** {@code cases} counted as the choices stand, beside the consistent ways already counted of
     *  them. */
    public static CaseCount of(DecidingCase.Cases cases,
                               NumericallyConsistentWays.Counted numericallyConsistentWays) {
        return of(cases, numericallyConsistentWays, Optional.empty());
    }

    /** The same, beside the ways a walk from the starts of the remainders would come to the end
     *  of ({@code walkedWaysAtMost}). */
    public static CaseCount of(DecidingCase.Cases cases,
                               NumericallyConsistentWays.Counted numericallyConsistentWays,
                               Optional<BigInteger> walkedWaysAtMost) {
        return new CaseCount(Ways.held(cases.structuralWays(WAYS_A_COUNT_IS_HELD_TO)),
                numericallyConsistentWays, walkedWaysAtMost);
    }
}
