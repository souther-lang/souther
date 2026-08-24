package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which arms no row goes through is the measure's answer to give, and there is no way round it.
 *
 * <p>Checked against the shape of the API rather than against an answer, for the reason
 * {@code NoPublicWayToTurnASpellingIntoATypeIdentityTest} gives: the rule had been written down
 * before and was broken all the same. A sentence is kept by whoever reads it; a signature is kept by
 * everyone.
 *
 * <p><b>What the rule is.</b> A query belongs to the type that can stand behind the answer, not to
 * the one that can work it out. {@code Arms} holds what was owed and what was seen, so the
 * difference is arithmetic it can do; the claim over that difference is that no row in the whole of
 * what was observed goes through those arms, and whether the whole of it could be read is the
 * measurement's to say. Put on the value, the query had to carry a sentence telling callers to ask
 * the measure first — which is the same defect issue #997 removed one level down, where an accessor
 * manufactured an empty answer for a caller who forgot to ask whether there was one.
 *
 * <p><b>Why the counts are not here.</b> {@code obligations} and {@code coveredObligations} stay on
 * the value and are right there. They are positive: a row that could not be read can only add to
 * what was seen, so what they state is true of what was observed however much of it that was. Only
 * the negative claim needs the reading to have finished.
 */
class ANegativeClaimIsOwnedByWhatCanStandBehindItTest {

    @Test
    void theArithmeticIsNotReachableFromOutsideThePackage() throws Exception {
        Method arithmetic = Adequacy.BranchEvidence.Arms.class.getDeclaredMethod("unreached");
        assertFalse(Modifier.isPublic(arithmetic.getModifiers()),
                "the value can work the arms out and cannot say they are unreached, so a reader"
                        + " outside cannot reach this without going through the measure");
    }

    @Test
    void theClaimIsTheMeasuresAndSaysWhenItCannotBeMade() throws Exception {
        Method claim = Adequacy.BranchEvidence.class.getDeclaredMethod("unreached");
        assertTrue(Modifier.isPublic(claim.getModifiers()), "and this is the way to it");
        assertEquals(Optional.class, claim.getReturnType(),
                "a measure that cannot make the claim says so by having no answer, rather than by"
                        + " an empty list that reads as no arm going unreached");
    }

    /**
     * And no accessor hands the value back so that a caller may ask it instead.
     *
     * <p>The shape this replaced. {@code armsReadInFull()} answered "may the claim be made" by
     * returning the arms, so the two halves — whether there is an answer and what it is — were two
     * calls with a protocol between them, and every surface kept that protocol on its own. A method
     * of this shape coming back is the protocol coming back.
     */
    @Test
    void noAccessorHandsTheValueOutForACallerToDrawTheClaimFrom() {
        List<String> capabilities = java.util.Arrays
                .stream(Adequacy.BranchEvidence.class.getDeclaredMethods())
                .filter(each -> Modifier.isPublic(each.getModifiers()))
                .filter(each -> each.getReturnType() == Optional.class)
                .filter(each -> each.getGenericReturnType().getTypeName()
                        .contains(Adequacy.BranchEvidence.Arms.class.getName()))
                .map(Method::getName).toList();

        assertEquals(List.of(), capabilities,
                "a measure that hands its value over under a name meaning `you may ask it` is the"
                        + " two-call protocol this removed");
    }
}
