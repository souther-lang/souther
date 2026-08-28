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
        Language said = plan(regex).compile(PatternPlan.Budget.OF_ADMITTED_VALUES);
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

    /**
     * A value somebody can paste is a different question from a string the language holds.
     *
     * <p>{@link Language#some} answers with what the language holds, preferring a written string
     * where one is no longer; {@link Language#someWritten} refuses to answer with anything else. A
     * caller writing a value into a model wants the second — a row carrying a control character is
     * not a row anybody can read back — and one deciding whether a language is empty wants the
     * first.
     *
     * <p>The two come apart exactly where every string a language holds is one a source cannot
     * carry, which is what the third of these is.
     */
    @Test
    void whatCanBeWrittenIsAskedApartFromWhatIsHeld() {
        String one = String.valueOf((char) 1);

        assertEquals("a", language("[a-z]").some());
        assertEquals("a", language("[a-z]").someWritten());

        // Shorter and unwritable beside longer and writable: what it holds is the short one, and
        // what can be written is the long one.
        Language either = language("[\\x{1}]|abc");
        // Written as a value rather than as itself: a control character pasted into a source is
        // what this whole question is about, and one sitting in the expectation would be the same
        // trap in the test.
        assertEquals(one, either.some());
        assertEquals("abc", either.someWritten());

        // And a language of nothing else has a string and no value to offer.
        Language unwritable = language("[\\x{1}-\\x{2}]+");
        assertEquals(one, unwritable.some());
        assertNull(unwritable.someWritten(),
                "every string it holds is one nobody can paste, so there is nothing to write");
    }

    /** And a plan of several is what those several come to. */
    @Test
    void aPlanOfSeveralIsWhatTheyComeTo() {
        Language both = plan("[0-9]+").and(plan("[0-4]{2}"))
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES);
        assertNotNull(both);
        assertTrue(both.has("00"));
        assertTrue(both.has("44"));
        assertFalse(both.has("55"));
        assertFalse(both.has("0"));

        Language either = plan("a+").or(plan("b+")).compile(PatternPlan.Budget.OF_ADMITTED_VALUES);
        assertNotNull(either);
        assertTrue(either.has("aa"));
        assertTrue(either.has("bb"));
        assertFalse(either.has("ab"));

        Language less = plan("[0-9]{2}").less(plan("00"))
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES);
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
        assertNotNull(big.compile(PatternPlan.Budget.OF_ADMITTED_VALUES), "and is built where there is room");
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
     * What comes back can be asked anything, and putting two of them together is what is allowed.
     *
     * <p>The two halves of what a language is. Asking is free — a compiled language holds the one
     * machine that accepts its strings, so every question below is read off what is in front of it.
     * Composing is charged, so each of these says what it is allowed and would answer null past it;
     * here there is room, and what the answers are is the point.
     */
    @Test
    void whatComesBackAnswersEverythingAskedOfIt() {
        Language one = language("[0-9]{2}");
        Language two = language("[0-4][0-9]");

        int allowed = PatternPlan.Budget.OF_ADMITTED_VALUES.mostStates();

        assertFalse(one.and(two, allowed).isEmpty());
        assertFalse(one.or(two, allowed).isEmpty());
        assertTrue(one.and(one.not(allowed), allowed).isEmpty());
        assertTrue(one.or(one.not(allowed), allowed).isEverything());
        assertEquals("00", one.and(two, allowed).some());
        assertTrue(one.and(two, allowed).has("40"));
    }

    /** A pattern outside the subset never reaches a plan, since a plan is made of what was read. */
    @Test
    void whatWasNotReadIsNotPlanned() {
        assertInstanceOf(PatternRead.NotRead.class, PatternParser.read("\\p{Alpha}"));
    }
}
