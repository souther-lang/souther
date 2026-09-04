package souther.compiler.check;

import souther.compiler.inputs.BlockReason;
import souther.compiler.values.ValueSet;

import java.util.List;

/**
 * Which strings one part of one clause admits at one position, published.
 *
 * <p>{@link StringRestriction} said the same thing while the reading was still going on, and said
 * it as a plan: which machine would answer the rule, with whether one is ever made left to the
 * position's allowance. This is what that came to. What crosses the boundary out of the reading is
 * the set — a reader downstream draws lines, writes reports and offers rows, and none of those is a
 * question that may decide what the model admits by building a machine of its own. Handed the plan,
 * every one of them could, and what a position is read to admit would have as many answers as it
 * has readers.
 *
 * <p>Three answers, and only the first two say anything about the rule. A rule whose strings were
 * worked out is a set to draw from, and one this compiler could not read is a rule the reader has
 * nothing about. The third says the position did not publish and says nothing else: why that
 * happened is what the position itself was short of and is answered there, so a rule that was
 * affordable is not made to carry a shortfall that is not about it.
 */
sealed interface AdmittedStrings {

    /** The strings the rule admits at the position, worked out. */
    record Admitting(ValueSet set) implements AdmittedStrings {

        public Admitting {
            if (set == null) {
                throw new IllegalArgumentException("a rule that was read admits some set");
            }
        }
    }

    /**
     * The rule is one about the strings and what it admits was not worked out, and what stopped the
     * reading.
     *
     * <p>The reading's own answer carried over ({@link StringRestriction.NotKnown}), because it is
     * a fact about the rule and this is where a reader meets it. Whether the rule states a boundary
     * is undecided here — not answered no — and what a report says about a question nothing settled
     * is the reason it was not settled.
     */
    record NotKnown(List<BlockReason.RuleReadingStopped> why) implements AdmittedStrings {

        public NotKnown {
            if (why.isEmpty()) {
                throw new IllegalArgumentException("a reading that stopped was stopped by something");
            }
            why = List.copyOf(why);
        }
    }

    /**
     * The rule is one about the strings and the position published none of its sets.
     *
     * <p>No reason of its own, and that is the whole of it. Whether a position's sets were built is
     * one answer for the whole of that position; this is a rule of such a position, kept so that a
     * reader walking the rules of a clause meets what it stated here rather than an absence, and
     * told nothing more because there is nothing about this rule to tell. The rule beside it may
     * have been affordable — one of them was not, and which is not something either of them
     * answers for.
     */
    record NotPublished() implements AdmittedStrings {}
}
