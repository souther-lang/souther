package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether two ends are one, asked of the order.
 *
 * <p>{@link Place} keeps this apart from what a value holds — {@code 0.00} and {@code 0} are one
 * line, and a reading keyed by the spelling has a position in two classes both holding zero. An end
 * is a place and an answer about the value standing at it, and it inherits the question: where a
 * range stops does not depend on how the rule that put it there wrote the number.
 *
 * <p>Here rather than at each reader. A record derives {@code equals} from what it holds, so an end
 * asked with one is asked about the spelling, and every caller wanting the order has to assemble the
 * comparison out of two halves. The two that decide which declaration is holding an end assembled it
 * wrongly, in the same way, in two places.
 */
class AnEndIsWhereARangeStopsAndNotHowItWasWrittenTest {

    /** The same place written two ways is one end, and the derived equality says otherwise. */
    @Test
    void onePlaceWrittenTwoWaysIsOneEnd() {
        Endpoint plain = at("3", true);
        Endpoint padded = at("3.00", true);

        assertTrue(plain.sameAs(padded), "3 and 3.00 are one place, so these stop in one spot");
        assertTrue(padded.sameAs(plain), "either way round");
        assertNotEquals(plain, padded,
                "which a derived equality does not answer, and is why this is asked here");
    }

    /** At one place, an end that admits the value and one that refuses it are two ends. */
    @Test
    void onePlaceAdmittedAndRefusedIsTwoEnds() {
        assertFalse(at("3", true).sameAs(at("3", false)),
                "one stops at 3 and the other stops short of it");
        assertFalse(at("3", false).sameAs(at("3.00", true)),
                "which the spelling does not change either");
    }

    /** Two places are two ends however they are written. */
    @Test
    void twoPlacesAreTwoEnds() {
        assertFalse(at("3", true).sameAs(at("10", true)), "3 is not 10");
        assertFalse(at("3.00", true).sameAs(at("3.01", true)), "nor is 3.00 3.01");
    }

    /** No end is not the same end as one that is there. */
    @Test
    void anEndThatIsNotThereIsNotThisOne() {
        assertFalse(at("3", true).sameAs(null), "there is nothing there to be the same as");
    }

    private static Endpoint at(String spelled, boolean inclusive) {
        return new Endpoint(new Count(new BigDecimal(spelled)), inclusive);
    }
}
