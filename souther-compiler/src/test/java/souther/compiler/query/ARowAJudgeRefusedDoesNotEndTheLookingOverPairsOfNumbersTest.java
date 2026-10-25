package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.Generator;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The pairs of numbers an answer turns on are looked over until a row is built whole and nothing
 * the judge refused: a row it refused is a row built, and the next pair may reach one it accepts.
 */
class ARowAJudgeRefusedDoesNotEndTheLookingOverPairsOfNumbersTest {

    @Test
    void aRowBuiltWholeAndAcceptedEndsTheLooking() {
        assertTrue(Adequacy.composedAgainstEverythingAsked(built(false)));
    }

    @Test
    void aRowBuiltWholeAndRefusedDoesNotEndIt() {
        assertFalse(Adequacy.composedAgainstEverythingAsked(built(true)));
    }

    private static Generator.BoundaryAttempt built(boolean refused) {
        return new Generator.BoundaryAttempt.Built(new Generator.GeneratedRow(
                new Generator.Purpose.ForAPoint("a rule of the decision"), List.of()),
                CompositionAccount.NOTHING, refused);
    }
}
