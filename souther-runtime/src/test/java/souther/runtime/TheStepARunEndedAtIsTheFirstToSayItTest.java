package souther.runtime;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * The step a run ended at is the first one to say it, as the run leaves the steps around it: a
 * step around it says nothing more, whether the first had a place to say or none, and a broken
 * constraint says its own place where it is refused.
 */
class TheStepARunEndedAtIsTheFirstToSayItTest {

    @Test
    void aStepAroundTheOneThatEndedTheRunDoesNotMoveIt() {
        ConstraintViolation ended = new ConstraintViolation("Int overflow: 1 + 9223372036854775807")
                .placedAt("lib", 3, 7);

        assertEquals(new ConstraintViolation.Site("lib", 3, 7), ended.placedAt("app", 9, 1).site());
    }

    @Test
    void aStepWithNoPlaceThatEndedTheRunIsNotTakenForTheOneAroundIt() {
        ConstraintViolation ended = new ConstraintViolation("division by zero: 1 / 0")
                .placedAt(null, 0, 0);

        assertNull(ended.placedAt("app", 9, 1).site());
    }

    @Test
    void aBrokenConstraintIsWhereItWasRefused() {
        ConstraintViolation refused = ConstraintViolation.notHeld(
                InvariantFailure.unnamed("lib", "Positive", "lib", "Positive", 0));

        assertSame(refused, refused.placedAt("app", 9, 1));
    }
}
