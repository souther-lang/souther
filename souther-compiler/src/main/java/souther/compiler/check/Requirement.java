package souther.compiler.check;

import souther.compiler.inputs.BlockReason;

/**
 * One thing a rule leaves at one place it is about: a question, or the fact that nothing worked out
 * which question there is.
 *
 * <p><b>Both, and at the same granularity.</b> A rule is read place by place, and how far the
 * reading got differs between them: {@code p.x < Int.multiply(p.y, p.y)} states something about the
 * values at {@code p.x} — a whole side of it is that position — and states nothing anybody here can
 * name about {@code p.y}, which the walk met inside a product it did not take apart. Written as one
 * answer for the rule, the second takes the first with it, and an obligation this compiler had
 * worked out is dropped because something beside it was not read.
 *
 * <p><b>{@link Undetermined#at} is where the classification stopped and not what the rule is
 * about.</b> What such a rule states there is what nothing worked out, so a reader may not turn the
 * place into a subject: it is where to look, which is what {@link souther.compiler.inputs
 * .FilingCoordinate} is for on the other side of the crossing, and it never becomes an
 * {@link Owed}.
 */
public sealed interface Requirement {

    /**
     * A question this rule raises here, worked out.
     *
     * <p>What answers it is asked afterwards. Which values may stand somewhere and where a line
     * falls are both this, and which of them it is, is the obligation's own.
     */
    record Determined(Owed owed) implements Requirement {

        public Determined {
            if (owed == null) {
                throw new IllegalArgumentException("a question this rule raises is one of them");
            }
        }
    }

    /**
     * A place this reading met and did not work out what the rule raises at.
     *
     * <p>Not "raises nothing", which is a conclusion about the rule and is {@link Required
     * .Irrelevant}'s to draw. Read as either of the two, a rule nobody could interpret is one the
     * model says nothing with, or one raising a question that could never be answered — and both
     * are claims about a model this compiler did not read.
     *
     * <p><b>Which question it is undecided about, and not merely that something is.</b> A rule can
     * be read far enough to say which values may stand somewhere and not far enough to say whether
     * it also puts a line there: {@code Decimal.compare(total, subtotal) <= 0} restricts what may
     * stand at {@code total} — the model says so whatever this compiler folds — and whether it
     * places an end there is what inverting the operation would answer. Held as one undecided
     * thing, the measure that answers the first is held open by the second.
     *
     * @param at    where the classification stopped, in the vocabulary of the value being read
     * @param which the question it was not worked out whether the rule raises. The measure this
     *              leaves open follows from it, exactly as it does for a question that was worked
     *              out
     * @param why   what this compiler could not do there, which is what would have to change
     *              before the rule could be classified
     */
    record Undetermined(RuleKey at, CoverageObligation which,
                        BlockReason.RuleReadingStopped why) implements Requirement {

        public Undetermined {
            if (at == null || which == null || why == null) {
                throw new IllegalArgumentException("a classification that did not come out is"
                        + " about one question, somewhere, for a reason");
            }
        }
    }
}
