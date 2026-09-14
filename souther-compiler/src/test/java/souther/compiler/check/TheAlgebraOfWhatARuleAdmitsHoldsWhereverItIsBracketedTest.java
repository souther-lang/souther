package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.values.AdmittedPlan;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a clause admits at a position does not turn on how its connectives were bracketed.
 *
 * <p>Three kinds of answer meet here — the strings a rule admits, every string where a reading
 * writes about the position without restricting it, and a rule this could not work out — and the
 * laws over them are the ones the plans already keep. Every string absorbs a choice and is the
 * identity of a conjunction; nothing at all absorbs a conjunction. Those hold whether or not the
 * other side was worked out, so a reading that stopped may not take an answer the law already gives.
 *
 * <p><b>Which is why this is a law and not a table of cases.</b> The same rules written with the
 * brackets moved are the same rules: {@code a || (b || c)} and {@code (a || b) || c} are one clause,
 * and a reading that answered them differently would make where a position's values stop turn on
 * something no author means. Written as cases, the first level was right and the composition of its
 * answer was not.
 */
class TheAlgebraOfWhatARuleAdmitsHoldsWhereverItIsBracketedTest {

    private static final StringRestriction PREFIX = new StringRestriction.Admitting(
            AdmittedPlan.of(ValueSet.oneOf(java.util.Set.of(Value.text("JP")))));
    private static final StringRestriction EVERY = StringRestriction.EVERY_STRING;
    private static final StringRestriction NONE =
            new StringRestriction.Admitting(AdmittedPlan.NONE);
    private static final StringRestriction UNKNOWN =
            new StringRestriction.NotKnown(new BlockReason.PatternTooDeeplyNested());
    private static final StringRestriction UNREAD =
            new StringRestriction.NotKnown(new BlockReason.UnreadValueRule());

    /** The answers a clause can come to at one position, which is what the laws are over. The last
     *  is a reading that writes nothing about the position, which is one of them. */
    private static final List<StringRestriction> EVERY_ANSWER =
            java.util.Arrays.asList(PREFIX, EVERY, NONE, UNKNOWN, null);

    /** Every string absorbs a choice, whatever the other side is and whether it was read. */
    @Test
    void everyStringAbsorbsAChoice() {
        for (StringRestriction each : EVERY_ANSWER) {
            assertAdmitsEveryString(join(EVERY, each), "every || " + each);
            assertAdmitsEveryString(join(each, EVERY), each + " || every");
            assertAdmitsEveryString(join(null, each), "nothing said || " + each);
            assertAdmitsEveryString(join(each, null), each + " || nothing said");
        }
    }

    /** And is the identity of a conjunction, on the same terms. */
    @Test
    void everyStringIsTheIdentityOfAConjunction() {
        for (StringRestriction each : EVERY_ANSWER) {
            assertEquals(said(each), meet(EVERY, each), "every && " + each);
            assertEquals(said(each), meet(each, EVERY), each + " && every");
            assertEquals(said(each), meet(null, each), "nothing said && " + each);
        }
    }

    /** Nothing at all absorbs a conjunction, read or not. */
    @Test
    void nothingAtAllAbsorbsAConjunction() {
        for (StringRestriction each : EVERY_ANSWER) {
            assertEquals(NONE, meet(NONE, each), "none && " + each);
            assertEquals(NONE, meet(each, NONE), each + " && none");
        }
    }

    /**
     * Moving the brackets of a choice does not move the answer.
     *
     * <p>The one this is here for. {@code unknown || (nothing said || prefix)} has an inner answer
     * of every string, so the whole is every string; bracketed the other way the inner answer is
     * the unknown one. Answered by a case for the absence rather than by the law, the two came out
     * different — and which of them an author got was where they put the brackets.
     */
    @Test
    void movingTheBracketsOfAChoiceDoesNotMoveTheAnswer() {
        for (StringRestriction one : EVERY_ANSWER) {
            for (StringRestriction two : EVERY_ANSWER) {
                for (StringRestriction three : EVERY_ANSWER) {
                    StringRestriction left = join(join(one, two), three);
                    StringRestriction right = join(one, join(two, three));
                    assertEquals(admitsEveryString(left), admitsEveryString(right),
                            one + " || " + two + " || " + three);
                    assertEquals(left instanceof StringRestriction.NotKnown,
                            right instanceof StringRestriction.NotKnown,
                            one + " || " + two + " || " + three);
                }
            }
        }
    }

    /** And of a conjunction. */
    @Test
    void movingTheBracketsOfAConjunctionDoesNotMoveTheAnswer() {
        for (StringRestriction one : EVERY_ANSWER) {
            for (StringRestriction two : EVERY_ANSWER) {
                for (StringRestriction three : EVERY_ANSWER) {
                    StringRestriction left = meet(meet(one, two), three);
                    StringRestriction right = meet(one, meet(two, three));
                    assertEquals(left instanceof StringRestriction.NotKnown,
                            right instanceof StringRestriction.NotKnown,
                            one + " && " + two + " && " + three);
                }
            }
        }
    }

    /**
     * Two readings that stopped keep both reasons, and in the order the clause writes them.
     *
     * <p>Two branches of one choice can be stopped by two different things, and those go out under
     * two different words. Keeping one, which of them a reader is shown would turn on which branch
     * the author wrote first.
     */
    @Test
    void twoReadingsThatStoppedKeepBothReasons() {
        StringRestriction.NotKnown both = assertInstanceOf(StringRestriction.NotKnown.class,
                join(UNKNOWN, UNREAD));
        assertEquals(List.of(new BlockReason.PatternTooDeeplyNested(),
                        new BlockReason.UnreadValueRule()), both.why());

        StringRestriction.NotKnown other = assertInstanceOf(StringRestriction.NotKnown.class,
                join(UNREAD, UNKNOWN));
        assertEquals(List.of(new BlockReason.UnreadValueRule(),
                new BlockReason.PatternTooDeeplyNested()), other.why());
    }

    /** The same reason twice is one reason: one rule stopped by one thing in two branches is not
     *  two things to say. */
    @Test
    void theSameReasonTwiceIsOneReason() {
        StringRestriction.NotKnown both = assertInstanceOf(StringRestriction.NotKnown.class,
                join(UNKNOWN, UNKNOWN));
        assertEquals(List.of(new BlockReason.PatternTooDeeplyNested()), both.why());
    }

    private static StringRestriction join(StringRestriction one, StringRestriction other) {
        return StringRestriction.over(one, other, false);
    }

    private static StringRestriction meet(StringRestriction one, StringRestriction other) {
        return StringRestriction.over(one, other, true);
    }

    /** What a reading that says nothing leaves, which is what it is compared against. */
    private static StringRestriction said(StringRestriction each) {
        return each == null ? EVERY : each;
    }

    private static boolean admitsEveryString(StringRestriction said) {
        return said instanceof StringRestriction.Admitting it
                && it.plan() instanceof AdmittedPlan.Everything;
    }

    private static void assertAdmitsEveryString(StringRestriction said, String what) {
        org.junit.jupiter.api.Assertions.assertTrue(admitsEveryString(said),
                () -> what + " came to " + said);
    }
}
