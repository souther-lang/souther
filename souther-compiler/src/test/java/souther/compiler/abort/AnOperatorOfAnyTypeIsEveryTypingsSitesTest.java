package souther.compiler.abort;

import org.junit.jupiter.api.Test;

import souther.compiler.types.BinOp;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an operator whose operands carry no type ends a run for is every reason a site its typings
 * are written as ends one for: the operator's own, and the construction a typing builds.
 */
class AnOperatorOfAnyTypeIsEveryTypingsSitesTest {

    /** {@code +} over a numeric newtype builds it again, and that construction is a site too. */
    @Test
    void aSumIsItsArithmeticAndTheNewtypeItMayBuildAgain() {
        assertEquals(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE,
                        AbortKind.INVARIANT_NOT_HELD),
                AbortSites.ofAnOperatorOfAnyType(BinOp.ADD));
    }

    /** {@code /} over a newtype answers a {@code Rational} and builds nothing. */
    @Test
    void aQuotientBuildsNothing() {
        assertEquals(AbortSet.of(AbortKind.DIVISION_BY_ZERO,
                        AbortKind.REQUIRED_FORM_HAS_NO_PLACE),
                AbortSites.ofAnOperatorOfAnyType(BinOp.DIV));
    }

    /** A comparison ends a run for nothing, whatever it compares. */
    @Test
    void aComparisonEndsNone() {
        assertEquals(AbortSet.NONE, AbortSites.ofAnOperatorOfAnyType(BinOp.EQ));
    }
}
