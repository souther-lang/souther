package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffinePreimage;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rational;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A coset whose values fill names one the run holds, however narrow the run is and whichever of its
 * ends is its own value.
 *
 * <p>Dense, so a run holding two members holds one between any two of them and there is nothing to
 * walk. What there is to do is name one — and naming it is a rounding, which is where an end the
 * rules exclude comes in. A rounding towards an excluded end lands on it and stays on it however
 * many decimal places it is asked for, so a run open at the bottom named nothing at all and what
 * came back was a value of the run that was no member of the coset.
 *
 * <p>Not a search: nothing here holds the value against anything but the run and the coset. What
 * makes it worth stating on its own is that a value off the coset is one the rest of the form cannot
 * finish, and a search handed one spends its whole allowance on a value that was never going to
 * work.
 */
class ACosetWhoseValuesFillNamesAMemberTheRunHoldsTest {

    private static NumericDomain.Bounds between(String low, boolean lowIsItsOwn, String high) {
        return new NumericDomain.Bounds(
                lowIsItsOwn ? Endpoint.inclusive(Count.of(new BigDecimal(low)))
                        : Endpoint.exclusive(Count.of(new BigDecimal(low))),
                Endpoint.inclusive(Count.of(new BigDecimal(high))));
    }

    /** Whether {@code at} is one of {@code from + by·d} for a decimal {@code d} a model writes. */
    private static boolean onTheCoset(Count at, Rational from, Rational by) {
        return Rational.of(at.at()).minus(from).dividedBy(by).asWrittenDecimal() != null;
    }

    private static Count named(CandidateDomain of) {
        return assertInstanceOf(CandidateDomain.Somewhere.class, of).at();
    }

    /**
     * The run's lower end is where the coset's own member sits, and the run does not hold it.
     *
     * <p>{@code 0 + 3·D} on {@code (0, 4]}. Zero is the member the arithmetic writes down and it is
     * the one value of the line the run excludes, so what is owed is the next one along.
     */
    @Test
    void aMemberOnAnExcludedEndIsSteppedOffRatherThanGivenUpOn() {
        CandidateDomain may = CandidateDomain.of(
                new AffinePreimage.Filling(Rational.ZERO, Rational.of(3)),
                between("0", false, "4"));

        Count at = named(may);
        assertTrue(between("0", false, "4").admits(at), "the run holds it: " + at);
        assertTrue(onTheCoset(at, Rational.ZERO, Rational.of(3)),
                "and it is a decimal multiple of three: " + at);
    }

    /**
     * The same where the run is narrower than the coset's generator, which is what the decimal places
     * are for.
     *
     * <p>{@code 0 + 3·D} on {@code (0, 0.05]} holds {@code 0.03} and nothing with fewer than two
     * places in it. What a run gives up on its own is the value halfway along, and two hundredths of
     * a whole is not three times any decimal.
     */
    @Test
    void aRunNarrowerThanTheGeneratorStillHoldsAMember() {
        CandidateDomain may = CandidateDomain.of(
                new AffinePreimage.Filling(Rational.ZERO, Rational.of(3)),
                between("0", false, "0.05"));

        assertTrue(between("0", false, "0.05").admits(named(may)), named(may).toString());
        assertTrue(onTheCoset(named(may), Rational.ZERO, Rational.of(3)), named(may).toString());
    }

    /**
     * A run too narrow for the places this writes says so, rather than naming a value off the coset.
     *
     * <p>{@code (0, 1e-30]} holds {@code 1e-30}, which is a decimal and so a member of every
     * decimal. Two dozen places do not reach it. What that settles is how far this was willing to
     * write and nothing at all about the coset, so the answer is neither a member nor a proof that
     * there is none.
     */
    @Test
    void aRunNoMemberIsWrittenInsideIsSaidToBeThatRatherThanAnsweredWithAnyValue() {
        CandidateDomain may = CandidateDomain.of(
                new AffinePreimage.Filling(Rational.ZERO, Rational.ONE),
                between("0", false, "1e-30"));

        assertInstanceOf(CandidateDomain.NotNamed.class, may);
    }

    /** An end that is its own value is taken as it stands, so the stepping above is not something
     *  this does to every run. */
    @Test
    void aMemberOnAnIncludedEndIsTheOneNamed() {
        CandidateDomain may = CandidateDomain.of(
                new AffinePreimage.Filling(Rational.ZERO, Rational.of(3)),
                between("0", true, "4"));

        assertEquals(Count.of(BigDecimal.ZERO), named(may));
    }
}
