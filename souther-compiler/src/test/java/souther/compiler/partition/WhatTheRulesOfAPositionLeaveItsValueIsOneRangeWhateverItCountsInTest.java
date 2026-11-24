package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.Type;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The numbers the rules a position wears leave its value are one range, whatever the position
 * counts in. Where it counts in whole numbers an end the rules do not reach is the whole number
 * inside it; anywhere else it is taken as reached, which holds every number the rules leave. A
 * side the rules leave open has no range.
 */
class WhatTheRulesOfAPositionLeaveItsValueIsOneRangeWhateverItCountsInTest {

    private static Endpoint inclusive(String at) {
        return Endpoint.inclusive(Count.of(new BigDecimal(at)));
    }

    private static Endpoint exclusive(String at) {
        return Endpoint.exclusive(Count.of(new BigDecimal(at)));
    }

    private static FormRange range(String least, String greatest) {
        return new FormRange(ExactRatio.of(new BigDecimal(least)),
                ExactRatio.of(new BigDecimal(greatest)));
    }

    private static final Carrier WHOLE = Carrier.ofPrimitive(Type.INT);
    private static final Carrier DECIMAL = Carrier.ofPrimitive(Type.DECIMAL);

    @Test
    void anEndTheRulesReachAreTheEndsOfTheRange() {
        assertEquals(range("0", "100"), FormRange.ofWhatTheRulesLeave(
                new DeclaredBounds.Range(inclusive("0"), inclusive("100"), WHOLE)));
        assertEquals(range("0.5", "99.5"), FormRange.ofWhatTheRulesLeave(
                new DeclaredBounds.Range(inclusive("0.5"), inclusive("99.5"), DECIMAL)));
    }

    @Test
    void anEndTheRulesDoNotReachIsTheWholeNumberInsideItWhereTheyCountInWholeNumbers() {
        assertEquals(range("1", "99"), FormRange.ofWhatTheRulesLeave(
                new DeclaredBounds.Range(exclusive("0"), exclusive("100"), WHOLE)));
        assertEquals(range("0", "100"), FormRange.ofWhatTheRulesLeave(
                new DeclaredBounds.Range(exclusive("0"), exclusive("100"), DECIMAL)));
    }

    @Test
    void aSideTheRulesLeaveOpenIsNoRange() {
        assertNull(FormRange.ofWhatTheRulesLeave(
                new DeclaredBounds.Range(exclusive("0"), null, DECIMAL)));
        assertNull(FormRange.ofWhatTheRulesLeave(
                new DeclaredBounds.Range(null, inclusive("1"), WHOLE)));
    }
}
