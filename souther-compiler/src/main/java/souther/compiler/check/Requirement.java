package souther.compiler.check;

import souther.compiler.inputs.BlockReason;

/**
 * One thing a rule leaves at one place it is about: a question, or the fact that nothing worked out
 * which question there is.
 *
 * <p><b>Both, and at the same granularity.</b> A rule is read place by place, and how far the
 * reading got differs between them: {@code lo >= 1 && Decimal.compare(a.value, b.value) <= 0}
 * states where the values at {@code lo} stop, and about {@code a} it speaks of what an operation
 * answered, so whether it puts an end there is what nothing worked out. Written as one answer for
 * the rule, the second takes the first with it, and an obligation this compiler had worked out is
 * dropped because something beside it was not read.
 *
 * <p><b>{@link BoundaryUndetermined#at} is where the classification stopped and not what the rule
 * is about.</b> What such a rule states there is what nothing worked out, so a reader may not turn
 * the place into a subject: it is where to look, which is what {@link souther.compiler.inputs
 * .FilingCoordinate} is for on the other side of the crossing, and it never becomes an
 * {@link Owed}.
 *
 * <p><b>One question is undecidable here and it is named.</b> Whether a rule restricts the values
 * at a name it writes is settled by its writing one — a rule about them is a rule about them
 * whether or not this compiler can say which ones — so the only classification that comes out
 * undecided is where the values stop. Held as an obligation and a reason, the arm would admit an
 * undecided admitted-values question, which nothing states and nothing could answer; the day one is
 * real it arrives as an arm of its own and every reader of these has to say what it does about it.
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
     * A place this reading met and did not work out whether the rule puts an end at.
     *
     * <p>Not "puts none", which is a conclusion about the rule and is what a clause read to the end
     * comes to. Read as either that or as an end nothing found, a rule nobody could interpret is
     * one the model draws no line with, or one owing a row at a line nobody can name — and both are
     * claims about a model this compiler did not read.
     *
     * <p>Which values may stand there is not in doubt beside it. {@code Decimal.compare(total,
     * subtotal) <= 0} restricts what may stand at {@code total} — the model says so whatever this
     * compiler folds — and whether it also places an end there is what inverting the operation
     * would answer. So the one is raised and the other is this, and only the border measure rests
     * on it.
     *
     * @param at  where the classification stopped, in the vocabulary of the value being read
     * @param why what this compiler could not do there, which is what would have to change before
     *            the rule could be classified. Every one of them, in the order the clause writes
     *            them: one clause read a branch at a time can be stopped by one thing in one branch
     *            and another in the next, and those go out under different words — so which of them
     *            a reader is shown may not turn on which branch was written first
     */
    record BoundaryUndetermined(RuleKey at, java.util.List<BlockReason.RuleReadingStopped> why)
            implements Requirement {

        public BoundaryUndetermined {
            if (at == null || why.isEmpty()) {
                throw new IllegalArgumentException("a classification that did not come out"
                        + " stopped somewhere, for a reason");
            }
            why = java.util.List.copyOf(why);
        }

        BoundaryUndetermined(RuleKey at, BlockReason.RuleReadingStopped one) {
            this(at, java.util.List.of(one));
        }
    }
}
