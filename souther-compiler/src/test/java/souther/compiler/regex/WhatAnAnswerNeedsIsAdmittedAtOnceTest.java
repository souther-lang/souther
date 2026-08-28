package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an answer needs of its patterns is admitted at once, and what comes back holds.
 *
 * <p>The cost of answering exactly is not a property of any one pattern. Two that are small on their
 * own have a meet the size of their product, so a bound put on each of them says nothing about the
 * two together — admitted one at a time, a language enters an answer and the work nobody could
 * afford happens later, where the only thing left is to fail inside an operation that is supposed to
 * be total.
 *
 * <p>So the plan is what is admitted. Either everything it names is built and a caller may ask the
 * language anything, or nothing is and the caller knows before anything became evidence.
 */
class WhatAnAnswerNeedsIsAdmittedAtOnceTest {

    private static PatternPlan plan(String regex) {
        return PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).syntax());
    }

    private static Language language(String regex) {
        Language said = plan(regex).compile(PatternPlan.Budget.OF_A_RULE);
        assertNotNull(said, regex + " is one a rule may be answered about");
        return said;
    }

    /** A plan of one pattern is that pattern's language. */
    @Test
    void aPlanOfOnePatternIsThatPattern() {
        Language one = language("T[0-9]{13}");

        assertTrue(one.has("T1234567890123"));
        assertFalse(one.has("T123456789012"));
        assertFalse(one.isEmpty());
        assertFalse(one.isEverything());
        assertEquals("T0000000000000", one.some());
    }

    /** And a plan of several is what those several come to. */
    @Test
    void aPlanOfSeveralIsWhatTheyComeTo() {
        Language both = plan("[0-9]+").and(plan("[0-4]{2}"))
                .compile(PatternPlan.Budget.OF_A_RULE);
        assertNotNull(both);
        assertTrue(both.has("00"));
        assertTrue(both.has("44"));
        assertFalse(both.has("55"));
        assertFalse(both.has("0"));

        Language either = plan("a+").or(plan("b+")).compile(PatternPlan.Budget.OF_A_RULE);
        assertNotNull(either);
        assertTrue(either.has("aa"));
        assertTrue(either.has("bb"));
        assertFalse(either.has("ab"));

        Language less = plan("[0-9]{2}").less(plan("00"))
                .compile(PatternPlan.Budget.OF_A_RULE);
        assertNotNull(less);
        assertTrue(less.has("01"));
        assertFalse(less.has("00"));
    }

    /**
     * A plan past what it is allowed comes to nothing, and never to something smaller.
     *
     * <p>What a plan says is which strings the answer is about. A language of fewer states is
     * another set, and a reader handed one would be measuring a model against something this
     * compiler made up because the real answer was expensive.
     */
    @Test
    void aPlanPastWhatItIsAllowedComesToNothing() {
        PatternPlan big = plan("[0-9]{5000}");

        assertNull(big.compile(new PatternPlan.Budget(100, 100)));
        assertNotNull(big.compile(PatternPlan.Budget.OF_A_RULE), "and is built where there is room");
    }

    /**
     * The whole of a plan is charged, and not each step on its own.
     *
     * <p>Which is the difference a bound per pattern cannot express. Every step here is well inside
     * what one machine may be, and what they come to together is not — so a plan admitted step by
     * step would be admitted, and the states nobody counted would be built anyway.
     */
    @Test
    void whatEveryStepCostsIsChargedTogether() {
        PatternPlan several = plan("[0-9]{40}").or(plan("[a-z]{40}"))
                .or(plan("[A-Z]{40}")).or(plan("[0-9a-z]{40}"));

        PatternPlan.Budget roomForOne = new PatternPlan.Budget(1_000, 100);

        assertNotNull(several.compile(new PatternPlan.Budget(1_000, 100_000)),
                "each of them is small, and together they fit where there is room for them");
        assertNull(several.compile(roomForOne),
                "and not where there is room for one of them at a time");
    }

    /**
     * What comes back can be asked anything.
     *
     * <p>The whole of what admitting a plan is for. A language that had to refuse an operation
     * afterwards would be one whose meet is not a set, and a reader would have to hold an answer
     * that might not have one.
     */
    @Test
    void whatComesBackAnswersEverythingAskedOfIt() {
        Language one = language("[0-9]{2}");
        Language two = language("[0-4][0-9]");

        assertFalse(one.and(two).isEmpty());
        assertFalse(one.or(two).isEmpty());
        assertTrue(one.and(one.not()).isEmpty());
        assertTrue(one.or(one.not()).isEverything());
        assertEquals("00", one.and(two).some());
        assertTrue(one.and(two).has("40"));
    }

    /** A pattern outside the subset never reaches a plan, since a plan is made of what was read. */
    @Test
    void whatWasNotReadIsNotPlanned() {
        assertInstanceOf(PatternRead.NotRead.class, PatternParser.read("\\p{Alpha}"));
    }
}
