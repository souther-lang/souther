package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.EnteredArm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition a way left unread is explained by a side kept under a key only where it is the
 * entering of the arm that finds that side's end.
 *
 * <p>A helper expanded at two places is two trees, each with an arm of the one match the source
 * wrote, and each arm binds a name of its own. A lookup that found a value in one is no lookup the
 * other made, so the condition that entered the one explains nothing of the end the other found.
 */
class TheArmThatFindsAKeysEndIsTheTreesArmAndNotTheSourcesTest {

    /** The name an arm binds in an expansion: one for each expansion of the same code. */
    private static EnteredArm armOfExpansion(int expansion) {
        return new EnteredArm(new BindingId(new BindingOwner.OfValue("example", "sinceOf"),
                expansion));
    }

    private static OnTheWay.Declined declinedAt(Optional<EnteredArm> arm) {
        ConditionOccurrence at = new ConditionOccurrence("f",
                ConditionOccurrence.Reading.DIVIDING, 0);
        return new OnTheWay.Declined(at, new ConditionReportAnchor.WhereTheReadingMetIt("m", at),
                List.of(new WhyNotTaken.OutsideDomain(
                        WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER)),
                arm);
    }

    private static Quantity.KeptSoFar.Seed foundBy(Optional<EnteredArm> arm) {
        return new Quantity.KeptSoFar.Seed.OfTheKey(TermPath.of("x"), arm);
    }

    @Test
    void theEnteringOfTheArmThatFoundTheEndExplainsIt() {
        assertTrue(UndividedByARelation.findsTheEndOf(declinedAt(Optional.of(armOfExpansion(0))),
                foundBy(Optional.of(armOfExpansion(0)))));
    }

    @Test
    void theEnteringOfTheSameCodesArmInAnotherExpansionExplainsNothingOfIt() {
        assertFalse(UndividedByARelation.findsTheEndOf(declinedAt(Optional.of(armOfExpansion(1))),
                foundBy(Optional.of(armOfExpansion(0)))));
    }

    @Test
    void aConditionThatEnteredNoArmExplainsNothing() {
        assertFalse(UndividedByARelation.findsTheEndOf(declinedAt(Optional.empty()),
                foundBy(Optional.of(armOfExpansion(0)))));
    }

    @Test
    void anEndHandedToAClosureIsFoundByNoArm() {
        assertFalse(UndividedByARelation.findsTheEndOf(declinedAt(Optional.of(armOfExpansion(0))),
                foundBy(Optional.empty())));
    }
}
