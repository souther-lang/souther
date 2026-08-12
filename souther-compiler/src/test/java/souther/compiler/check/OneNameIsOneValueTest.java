package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name the discharge check gives an atom is a name for one value.
 *
 * <p>Every relation the numeric domain records is recorded against a name, so two values under one
 * name is every relation about one of them read as a relation about the other. The kind of number
 * behind a name is what catches it: a whole number and a dense one are not the same value however
 * alike they are written.
 *
 * <p>Held here because the check is fail-open. A walk that falls over produces what a walk that found
 * nothing produces, so a contradiction inside the check would arrive as a behavior with no findings —
 * silence that reads as every invariant discharged. What this holds is that one failure is refused
 * rather than recorded: the check may be unable to answer for a program, and it may not disagree with
 * itself about its own names.
 */
class OneNameIsOneValueTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static BindingId binding() {
        return new BindingId(new BindingOwner.OfValue("demo", "f"), 0);
    }

    @Test
    void oneKeyIsRefusedASecondKindOfNumber() {
        Terms terms = new Terms(Symbols.none());
        BindingId binding = binding();
        Denotations at = Denotations.none().location(binding);
        String whole = terms.atomOf(new Core.Read("n", binding, Type.INT, POS), at);
        assertNotNull(whole, "a location is an atom");
        Terms.OneKeyTwoKinds refused = assertThrows(Terms.OneKeyTwoKinds.class,
                () -> terms.atomOf(new Core.Read("n", binding, Type.DECIMAL, POS), at),
                "the same name, standing for a number spaced the other way");
        assertTrue(refused.getMessage().contains(whole),
                "and it says which name: " + refused.getMessage());
    }

    @Test
    void theCheckDoesNotSwallowItsOwnContradiction() {
        assertThrows(Terms.OneKeyTwoKinds.class,
                () -> InvariantChecker.gaveUp("analyze",
                        new Terms.OneKeyTwoKinds("atom `n` is DISCRETE and DENSE")),
                "recording it would leave a behavior looking like one with nothing to report");
    }

    @Test
    void andStillGivesUpOnAShapeItHasNoRuleFor() {
        assertDoesNotThrow(() -> InvariantChecker.gaveUp("analyze",
                        new IllegalStateException("something the walk has no rule for")),
                "which is what fail-open is for");
    }
}
