package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the strings of a position reach is claimed per kind of claim, and each claim holds only
 * where its premises do: a rule on one number of a string keeps another number from being reached
 * freely, a rule not read leaves no value shown, and a position only some values have is not one
 * every value of the input needs.
 */
class WhatTheStringsOfAPositionReachIsAskedOfThePositionTest {

    private static StringsReached reached(String model) {
        return PartitionsTest.partitioningOf(model, "f").strings();
    }

    private static final String ANY = """
            module example.any

            behavior f : (s: String) -> Int

            let f (s) = if String.length(s) >= 3 then 1 else 0
            """;

    private static final String SHORT = """
            module example.short

            data Short = String
                invariant String.length(value) <= 2

            behavior f : (s: Short) -> Int

            let f (s) = 1
            """;

    private static final String UNREAD = """
            module example.unread

            data Nothing = String
                invariant String.reverse(value) /= String.reverse(value)

            behavior f : (s: Nothing) -> Int

            let f (s) = 1
            """;

    private static final String NEVER_FIELD = """
            module example.neverfield

            data Never = String
                invariant String.matches("a\\\\x{301}.*", value)

            data Holder = { label: Never, n: Int }

            behavior f : (h: Holder) -> Int

            let f (h) = 1
            """;

    private static final String NEVER_ELEMENT = """
            module example.neverelement

            data Never = String
                invariant String.matches("a\\\\x{301}.*", value)

            data Holder = { items: List<Never>, n: Int }

            behavior f : (h: Holder) -> Int

            let f (h) = 1
            """;

    @Test
    void aStringNoRuleBoundsReachesEverySumAndCount() {
        StringsReached strings = reached(ANY);
        assertTrue(strings.mandatoryPositionsHoldAValue());
        assertFalse(strings.countsReached().isEmpty(), "the control: nothing binds the sums");
    }

    @Test
    void aRuleOnTheLengthKeepsTheSumsFromBeingReachedFreely() {
        StringsReached strings = reached(SHORT);
        assertTrue(strings.mandatoryPositionsHoldAValue(), "the position holds a value");
        assertTrue(strings.countsReached().isEmpty(),
                "two code points come to at most twice the largest, so not every sum is reached");
    }

    @Test
    void aPositionWhoseRulesWereNotReadInFullIsReachedInNothing() {
        StringsReached strings = reached(UNREAD);
        assertTrue(strings.countsReached().isEmpty());
        assertTrue(strings.lengthsReached().isEmpty());
    }

    @Test
    void aFieldHoldingNoValueLeavesTheInputNone() {
        assertFalse(reached(NEVER_FIELD).mandatoryPositionsHoldAValue());
    }

    @Test
    void anElementHoldingNoValueLeavesTheInputItsEmptyCollection() {
        assertTrue(reached(NEVER_ELEMENT).mandatoryPositionsHoldAValue(),
                "the empty list is a value, so no value of the input needs an element");
    }
}
