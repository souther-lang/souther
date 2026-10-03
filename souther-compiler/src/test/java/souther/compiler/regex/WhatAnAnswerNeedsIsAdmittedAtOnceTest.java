package souther.compiler.regex;

import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import org.junit.jupiter.api.Test;

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
                PatternParser.read(regex), regex).meaning());
    }

    /** A plan of several is what those several come to. */
    @Test
    void aPlanOfSeveralIsWhatTheyComeTo() {
        Language both = plan("[0-9]+").and(plan("[0-4]{2}"))
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
        assertNotNull(both);
        assertTrue(both.has("00"));
        assertTrue(both.has("44"));
        assertFalse(both.has("55"));
        assertFalse(both.has("0"));

        Language either = plan("a+").or(plan("b+")).compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
        assertNotNull(either);
        assertTrue(either.has("aa"));
        assertTrue(either.has("bb"));
        assertFalse(either.has("ab"));

        Language less = plan("[0-9]{2}").less(plan("00"))
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
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

        assertNull(big.compile(new PatternPlan.Budget(100, 100, 1_000_000_000L).meter()));
        assertNotNull(big.compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter()), "and is built where there is room");
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

        PatternPlan.Budget roomForOne = new PatternPlan.Budget(1_000, 100, 1_000_000_000L);

        assertNotNull(several.compile(new PatternPlan.Budget(1_000, 100_000, 1_000_000_000L).meter()),
                "each of them is small, and together they fit where there is room for them");
        assertNull(several.compile(roomForOne.meter()),
                "and not where there is room for one of them at a time");
    }
}
