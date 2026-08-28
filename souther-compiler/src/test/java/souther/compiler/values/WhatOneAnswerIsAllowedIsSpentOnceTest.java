package souther.compiler.values;

import org.junit.jupiter.api.Test;

import souther.compiler.regex.Language;
import souther.compiler.regex.Meter;
import souther.compiler.regex.PatternParser;
import souther.compiler.regex.PatternPlan;
import souther.compiler.regex.PatternRead;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What one answer is allowed to cost is spent on that answer, once, and says so when it runs out.
 *
 * <p>The resource model, held to on its own. What a position finally admits is met out of every
 * rule that reached it, so the thing being paid for is the answer and not any of the rules: two
 * patterns each affordable on its own have a meet the size of their product, and a bound put on
 * each of them says nothing about the two together.
 *
 * <p>Four things are asked of it, and each is a way the model could be wrong while every set it
 * produced was still an upper bound — which is why none of them can be seen by asking what a
 * reading came to. The allowance is cumulative at a position, it is not shared between positions,
 * running out of it blames no rule, and none of it turns on the order the rules were written in.
 */
class WhatOneAnswerIsAllowedIsSpentOnceTest {

    private static final String HERE = "here";
    private static final String THERE = "there";

    private static Language language(String regex) {
        PatternRead read = PatternParser.read(regex);
        Language made = PatternPlan.of(assertInstanceOf(PatternRead.Read.class, read, regex)
                .syntax()).compile(PatternPlan.Budget.OF_ADMITTED_VALUES);
        assertNotNull(made, regex);
        return made;
    }

    /**
     * Digits, however many of them, so long as how many is a multiple of {@code every}.
     *
     * <p>Chosen because two of these meet to a third of the same shape and never to nothing: the
     * lengths a meet admits are the multiples of both, so the machine is as many states as the two
     * numbers multiply to. Patterns of a fixed length would do the arithmetic and then admit
     * nothing — {@code [0-9]{3}} and {@code [0-9]{4}} share no string — and a meet that comes to
     * the empty set is one this compiler builds no machine for.
     */
    private static ValueSet everyMultipleOf(int every) {
        return ValueSet.matching(language("(?:[0-9]{" + every + "})+"));
    }

    /** More than anything here asks for, so that a measurement is of the work and not of a limit. */
    private static final int PLENTY = 10_000_000;

    /**
     * What meeting these two actually takes, in states made.
     *
     * <p>Measured and never worked out. What a meet costs is not the sizes of its operands nor the
     * size of what it comes to — the machine put together is larger than either, and making it
     * canonical makes another — so an allowance set from arithmetic is one this test would never
     * reach. Asked of the meter, which is the only thing that knows ({@link Meter}).
     */
    private static int costOfMeeting(ValueSet one, ValueSet other) {
        Meter meter = new Meter(PLENTY, PLENTY);
        assertNotNull(language(one).and(language(other), meter), "and it is built at all");
        return PLENTY - meter.left();
    }

    private static Language language(ValueSet set) {
        return assertInstanceOf(ValueSet.Matching.class, set).language();
    }

    /** An allowance of {@code inAll} states in all, no one machine being larger than the lot. */
    private static Sets<String> allowing(int inAll) {
        return Sets.of(new PatternPlan.Budget(inAll, inAll));
    }

    /**
     * Two compositions at one position spend from one purse.
     *
     * <p>Which is the whole of what "per answer" means. Each of these is affordable on its own and
     * the three of them are not, so an allowance that started again at each composition would build
     * all of them and this test would pass for a compiler that had no bound at all.
     */
    @Test
    void whatIsSpentAtOnePositionAccumulates() {
        ValueSet three = everyMultipleOf(3);
        ValueSet four = everyMultipleOf(4);
        ValueSet five = everyMultipleOf(5);

        // What the two meets take, measured rather than reckoned.
        ValueSet both = allowing(PLENTY).meet(HERE, three, four).set();
        int first = costOfMeeting(three, four);
        int second = costOfMeeting(both, five);

        // Room for either meet on its own, and one state short of room for both. So the only thing
        // that can refuse the second is what the first one spent.
        Sets<String> sets = allowing(first + second - 1);

        assertFalse(sets.meet(HERE, three, four).gaveUp(),
                "the first meet fits, which is what the allowance was set to");
        Sets.Composed met = sets.meet(HERE, both, five);
        assertTrue(met.gaveUp(),
                "and the second does not, once the first has been paid for out of the same purse");
        assertEquals(ValueSet.ANY, met.set(), "what is left is every value, which is true");

        // The control, and what makes the sentence above about accumulation rather than about a
        // ceiling: the same allowance, untouched, builds the very meet it just refused.
        assertFalse(allowing(first + second - 1).meet(HERE, both, five).gaveUp(),
                "the second meet is within the allowance where nothing has been spent from it");
    }

    /**
     * And what one position spends is not taken from another.
     *
     * <p>A position whose rules are complicated may not make the position beside it unanswerable.
     * Held with the same two compositions at two positions: neither is short, where the two of them
     * at one position were.
     */
    @Test
    void onePositionDoesNotSpendWhatAnotherWasGoing() {
        ValueSet three = everyMultipleOf(3);
        ValueSet four = everyMultipleOf(4);
        // Enough for one such meet and not for two, so that a shared purse would be seen.
        Sets<String> sets = allowing(costOfMeeting(three, four));

        assertFalse(sets.meet(HERE, three, four).gaveUp());
        assertFalse(sets.meet(THERE, three, four).gaveUp(),
                "the other position has its own allowance and has spent none of it");
        assertEquals(java.util.Set.of(), sets.spent());
    }

    /**
     * Running out blames no rule, and the reading says which position it was.
     *
     * <p>The attribution the whole arrangement rests on. Both patterns were read — each compiles on
     * its own — so neither of them is a rule anybody could rewrite to make this go away, and what
     * is recorded is the position whose answer was not built. {@link Sets.Composed} carries the
     * widening and the shortfall together, so a caller cannot take the one and drop the other.
     */
    @Test
    void runningOutBlamesThePositionAndNoRule() {
        ValueSet four = everyMultipleOf(4);
        ValueSet five = everyMultipleOf(5);
        // Enough for either pattern and not for what they come to, which is the whole point: each
        // was read, and it is the answer between them that was not built.
        Sets<String> sets = allowing(costOfMeeting(four, five) - 1);

        Sets.Composed made = sets.meet(HERE, four, five);

        assertTrue(made.gaveUp());
        assertEquals(ValueSet.ANY, made.set());
        assertEquals(java.util.Set.of(HERE), sets.spent(),
                "the position whose answer was not built, and nothing about either rule");
    }

    /**
     * And an answer nobody could afford is not written down as a rule going unread.
     *
     * <p>The other half of the sentence above, said where a reader picks it up. Two readings met
     * across declarations were each read in full where they were written — {@code whyPartial} is
     * the question about rules and there is no rule to answer it with — and what stands between the
     * set and the rules is the cost of putting them together. Written as {@link
     * AdmissibleSet.Widening.RuleUnread}, a reader would be sent to find a rule to rewrite, and for
     * a product of two affordable rules there is none.
     */
    @Test
    void anAnswerNobodyCouldAffordNamesNoUnreadRule() {
        AdmissibleSet unaffordable = AdmissibleSet.wider(ValueSet.ANY,
                java.util.Set.of(new AdmissibleSet.Widening.ExactValuesTooCostly()));

        assertTrue(unaffordable.exactValuesTooCostly());
        assertEquals(null, unaffordable.whyPartial(),
                "no rule went unread, so there is no rule to name");
        assertFalse(unaffordable.alternativesNotSeparated(),
                "and it is not the alternatives either, which every rule being read also allows");
        assertFalse(unaffordable.completeness() instanceof AdmissibleSet.Completeness.Complete,
                "what it is is a set this reading cannot show is what the rules leave");
    }

    /**
     * And what comes of it does not turn on the order the rules were written in.
     *
     * <p>The property a cumulative allowance is most easily got wrong by. Where three rules meet at
     * a position and the three of them are more than the answer is allowed, every order has to come
     * to the same thing — otherwise which rule is left out of the answer, and whether the answer is
     * exact at all, is decided by where an author happened to write a clause.
     */
    @Test
    void noOrderOfTheRulesLeavesADifferentAnswer() {
        List<ValueSet> rules =
                List.of(everyMultipleOf(3), everyMultipleOf(4), everyMultipleOf(5));
        // Room for one of these meets and not for the two, so that some order is refused and the
        // question is whether which one turns on the writing.
        int allowed = costOfMeeting(rules.get(0), rules.get(1));
        List<String> came = new ArrayList<>();

        for (List<Integer> order : List.of(List.of(0, 1, 2), List.of(0, 2, 1), List.of(1, 0, 2),
                List.of(1, 2, 0), List.of(2, 0, 1), List.of(2, 1, 0))) {
            Sets<String> sets = allowing(allowed);
            ValueSet held = rules.get(order.get(0));
            boolean gaveUp = false;
            for (int at = 1; at < order.size(); at++) {
                Sets.Composed made = sets.meet(HERE, held, rules.get(order.get(at)));
                held = made.set();
                gaveUp |= made.gaveUp();
            }
            came.add(order + " -> " + held + ", short: " + gaveUp
                    + ", spent at: " + sets.spent());
        }

        assertEquals(1, new java.util.LinkedHashSet<>(
                        came.stream().map(each -> each.substring(each.indexOf("->"))).toList())
                        .size(),
                "one answer and one account of it, whichever order the rules arrived in: " + came);
    }
}
