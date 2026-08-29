package souther.compiler.check;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The arithmetic every reader that opens a case split holds itself to, on its own.
 *
 * <p>Read here and not off a program, because what it says is about the arithmetic and not about
 * any one reader. {@link HowFarSplitsAreOpenedIsBoundedByHowFarTheyCompoundTest} holds the other
 * end — that the walk over a region really asks this and really stops where it answers no — and a
 * reader asking it for the first time ({@link DerivedBounds}, at #973) inherits what is stated here
 * rather than restating it.
 *
 * <p>What is bounded is the compounding and not the number of contexts. Two of these below reach a
 * factor past the limit and are right to: a split one arm wide multiplies nothing, and the first
 * split that does multiply is opened however wide it is. A test asserting {@code factor <= 16}
 * anywhere would be asserting something this does not claim.
 */
class WhatSplitsCopyAReadingToIsBoundedWhereTheyCompoundTest {

    private static ContextMultiplicity one() {
        return ContextMultiplicity.ofOneReading();
    }

    /** Where every reader begins, and the limit it holds itself to. */
    @Test
    void aReaderBeginsAtOneReadingUnderTheOneLimit() {
        assertEquals(1, one().factor());
        assertEquals(ContextMultiplicity.CONTEXT_COMPOUNDING_LIMIT, one().compoundingLimit());
    }

    /** Nothing has multiplied yet, so the width is what the readings come to whatever it is. */
    @Test
    void theFirstSplitIsOpenedHoweverWideItIs() {
        assertEquals(100, one().opening(100).factor());
    }

    /** And past the limit is where it leaves the path, so what follows is refused. */
    @Test
    void whatFollowsAFirstSplitWiderThanTheLimitIsRefused() {
        assertNull(one().opening(100).opening(2));
    }

    /** A split one arm wide copies a reading once, which is the reading it already was. Answered
     * with the same value and not an equal one: there is nothing to compute. */
    @Test
    void aSplitOneArmWideIsTheIdentity() {
        ContextMultiplicity far = one().opening(100);
        assertSame(far, far.opening(1));
        assertSame(far, far.opening(1).opening(1).opening(1));
    }

    /** Which holds at one reading as much as past the limit. */
    @Test
    void aSplitOneArmWideIsTheIdentityAtOneReadingToo() {
        ContextMultiplicity begun = one();
        assertSame(begun, begun.opening(1));
    }

    /** Four and four is sixteen, which is the limit, and a two after it is thirty-two. */
    @Test
    void fourAndFourReachTheLimitAndATwoAfterThemDoesNot() {
        ContextMultiplicity at16 = one().opening(4).opening(4);
        assertEquals(16, at16.factor());
        assertNull(at16.opening(2));
    }

    /** Three and five is fifteen, which is inside it, and a two after it is thirty. So what is
     * asked is what opening the split would come to and not what the path has come to already. */
    @Test
    void threeAndFiveStayInsideItAndATwoAfterThemDoesNot() {
        ContextMultiplicity at15 = one().opening(3).opening(5);
        assertEquals(15, at15.factor());
        assertNull(at15.opening(2));
    }

    /** Four twos are sixteen and a fifth is thirty-two: the same limit the widths above reach, at a
     * depth instead of a width. */
    @Test
    void fourTwosReachTheLimitAndAFifthDoesNot() {
        ContextMultiplicity at16 = one().opening(2).opening(2).opening(2).opening(2);
        assertEquals(16, at16.factor());
        assertNull(at16.opening(2));
    }

    /** A split refused under one limit is opened under any larger one, and nothing an answer says
     * comes back wider for the room. Raising the limit buys precision and invents nothing. */
    @Test
    void aLargerLimitOpensWhatASmallerOneRefusesAndChangesNothingElse() {
        ContextMultiplicity tight = new ContextMultiplicity(1, 8).opening(4);
        ContextMultiplicity roomy = new ContextMultiplicity(1, 32).opening(4);
        assertEquals(tight.factor(), roomy.factor());
        assertNull(tight.opening(4));
        assertNotNull(roomy.opening(4));
        assertEquals(16, roomy.opening(4).factor());
    }

    /** Asking answers and does not spend: two arms of one split ask the same question of the same
     * value and are told the same thing, which is what makes a split all-or-none rather than a
     * budget the arms draw down in the order they were written. */
    @Test
    void askingTwiceAnswersTwiceTheSame() {
        ContextMultiplicity at4 = one().opening(2).opening(2);
        assertEquals(at4.opening(4).factor(), at4.opening(4).factor());
        assertEquals(4, at4.factor());
    }

    /** A split answers one of several, so none of these is a split. */
    @Test
    void aSplitWithNoArmsIsNotAWidthThisAnswersAbout() {
        assertThrows(IllegalArgumentException.class, () -> one().opening(0));
        assertThrows(IllegalArgumentException.class, () -> one().opening(-1));
    }

    /** A reading is copied at least once, and a limit admits at least the reading itself. */
    @Test
    void aFactorAndALimitBelowOneAreNotStatesThisHolds() {
        assertThrows(IllegalArgumentException.class, () -> new ContextMultiplicity(0, 16));
        assertThrows(IllegalArgumentException.class, () -> new ContextMultiplicity(1, 0));
    }
}
