package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * The two facts a question a rule raised can stand on, held apart because no order runs across
 * them.
 *
 * <p>A part of the rule a reading gave up on belongs to something somebody wrote and stands where
 * they wrote it. A limit the position's answer ran into belongs to what the rules of that position
 * come to between them — the same rules met in another order would have been built — so it belongs
 * to no part of the rule and there is nothing written for it to stand after or before.
 *
 * <p><b>Held in one sequence, the two acquire a precedence the model does not have.</b> Nothing
 * says a form nothing reads comes before an allowance that ran out, or after it; a document writing
 * them as one list says one of those anyway, and a reader acting on the order is acting on a fact
 * about which store a reason was recorded in. So they are two, here and out there.
 *
 * <p>At least one, because a question stands for a reason. Both where both hold: a rule with a
 * conjunct nothing reads, written beside a choice whose meet ran past the allowance, is short in
 * two ways that different work lifts.
 *
 * @param itsRuleLeft what the parts of the rule left, saying whether that is an order anybody
 *                    wrote ({@link RuleReasons}). Carried and not decided: what settles it is the
 *                    places the reasons stand on, and those are gone by the time anything here
 *                    holds a word
 * @param itsPositionWasShortOf what its position's answer was short of, which names no part of the
 *                              rule and so has no place among them
 */
public record WhatAQuestionStandsOn(
        RuleReasons itsRuleLeft,
        Optional<BlockReason.AnswerRealizationStopped> itsPositionWasShortOf) {

    public WhatAQuestionStandsOn {
        if (itsRuleLeft == null || itsPositionWasShortOf == null) {
            throw new IllegalArgumentException("a question stands on what its rule left and on what"
                    + " its position was short of, and says which it has");
        }
        if (itsRuleLeft.isEmpty() && itsPositionWasShortOf.isEmpty()) {
            throw new IllegalArgumentException(
                    "a question stands because something was short of it");
        }
    }

    /**
     * One limit the answer ran into, out of what the position was short of.
     *
     * <p>A second is refused rather than put in an order. There is one such reason today; a second
     * would be a pair with no order between them either, and what a document should then write is a
     * decision to take when there is something to decide about — taken here by silence, it would be
     * taken by whichever arrived first.
     */
    public static Optional<BlockReason.AnswerRealizationStopped> oneOf(
            List<BlockReason.AnswerRealizationStopped> recorded) {
        BlockReason.AnswerRealizationStopped out = null;
        for (BlockReason.AnswerRealizationStopped each : recorded) {
            if (out != null && !out.equals(each)) {
                throw new IllegalArgumentException(
                        "two limits the answer ran into stand at one question with no order"
                                + " between them: " + out + " and " + each);
            }
            out = each;
        }
        return Optional.ofNullable(out);
    }

    /**
     * Both, as the one list the readers that ask what a measure is short of read.
     *
     * <p>Whether a wider run gets past a question is asked of everything it stands on, and that
     * reader has no use for which store a reason came from. What it must not do is read an order
     * off this — there is none across the two — which is why the order lives in
     * {@link #itsRuleLeft} and nowhere else.
     */
    public List<BlockReason.QuestionStandingReason> all() {
        List<BlockReason.QuestionStandingReason> out = new ArrayList<>(itsRuleLeft.reasons());
        itsPositionWasShortOf.ifPresent(out::add);
        return List.copyOf(out);
    }
}
