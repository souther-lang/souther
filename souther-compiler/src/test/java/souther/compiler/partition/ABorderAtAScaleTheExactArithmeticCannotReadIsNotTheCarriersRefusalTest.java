package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.UnheldNumber;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A run whose two ends a model's own decimals put far enough apart in scale that the exact
 * arithmetic cannot round either end inward is not read as an ordinary empty run.
 *
 * <p>{@link LevelInterval#digitsToLookIn} needs an {@code int} count of how many digits separate a
 * run's two ends before either can be rounded inward, and a model whose own decimals put one end at
 * an ordinary place and the other at a scale no {@code int} holds is a run this compiler could not
 * read at all — {@link Occupancy.NotWorkedOut}, and never {@link Occupancy.Empty}, which is what
 * every reader downstream of {@link LevelSpace#inspect} used to be handed instead and read as a
 * proof this order has no value there.
 */
class ABorderAtAScaleTheExactArithmeticCannotReadIsNotTheCarriersRefusalTest {

    /** A decimal so many powers of two past an ordinary one that telling the two apart by scale is
     *  past what an {@code int} digit count can hold. */
    private static final ExactRatio OUTSCALED =
            new ExactRatio(BigInteger.ONE, BigInteger.ONE, 5_000_000_000L, 0);

    private static Level at(ExactRatio value) {
        return new Level.OfTheQuantity(value);
    }

    /** The run from an ordinary decimal up to one outscaled past it, on the carrier every plain
     *  {@code Decimal} position uses. */
    private static LevelInterval theOutscaledRun() {
        return new LevelInterval(Bound.at(at(ExactRatio.ONE), true), Bound.at(at(OUTSCALED), true));
    }

    private static LevelSpace decimals() {
        return LevelSpace.onACarrier(new Carrier.Dense());
    }

    /** The run itself: not an empty one, and not a proof either — a refusal this compiler is honest
     *  about having made, in the one of the two ways such a scale actually fails. */
    @Test
    void theRunIsNeitherEmptyNorInhabitedButNotWorkedOut() {
        Occupancy occupancy = decimals().inspect(theOutscaledRun());

        Occupancy.NotWorkedOut notWorkedOut = assertInstanceOf(Occupancy.NotWorkedOut.class,
                occupancy, "a run no digit count can hold is not this order's own answer either way");
        assertEquals(UnheldNumber.NO_REPRESENTATION_EXISTS, notWorkedOut.why(),
                "a digit count is an int by this type's own contract, and no int names this many");
    }

    /**
     * An ordinary run of the same shape — one end at an ordinary place, the other close enough that
     * the digit count between them is cheap — is read as a genuine answer, so the refusal above is
     * this run's own scale and not something every bounded run gets told.
     */
    @Test
    void anOrdinaryRunOfTheSameShapeIsReadAsAGenuineAnswer() {
        LevelInterval ordinary = new LevelInterval(
                Bound.at(at(ExactRatio.ONE), true), Bound.at(at(ExactRatio.of(100)), true));

        Occupancy occupancy = decimals().inspect(ordinary);

        assertInstanceOf(Occupancy.Inhabited.class, occupancy);
        assertNotEquals(new Occupancy.Empty(), occupancy);
    }
}
