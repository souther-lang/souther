package souther.compiler.check;

import souther.compiler.inputs.BlockReason;

/**
 * Whether a rule raises one coverage question at one place: it does, it does not, or nothing worked
 * out which.
 *
 * <p>Three answers and not two, and the third is not the absence of the first. A rule this compiler
 * read to the end that draws no line places none — that is the model, and no reading of it would
 * change the answer — while a rule whose form nothing took apart may place one and may not, and
 * saying so is what keeps a measure from closing over it. Written as "raises it or does not", the
 * second is whichever of the two whoever wrote the classification happened to reach for.
 *
 * <p><b>Asked for every question and at every place.</b> What refuses a question nobody classified
 * is the switch over {@link CoverageObligation} that answers this, which has no {@code default}: a
 * word added there stops the build until somebody says what a clause raises under it. What this
 * type adds is that the answer they have to write is one of three and not the absence of one — a
 * place that raises nothing says so, rather than being a place nothing was recorded about.
 */
sealed interface ObligationClassification {

    /** The rule raises it, and this is the question. */
    record Raised(Owed owed) implements ObligationClassification {

        public Raised {
            if (owed == null) {
                throw new IllegalArgumentException("a question the rule raises is one of them");
            }
        }
    }

    /**
     * The rule does not raise it, which is a conclusion about the rule.
     *
     * <p>{@code value == 7} says which values may stand and draws no line; there is no end for
     * anything to be owed at, and no reading would find one. Reached only by classifying what a
     * reader found the clause to state, like every other answer here.
     */
    record NotRaised() implements ObligationClassification {}

    /**
     * Nothing worked out whether it raises it.
     *
     * <p>The reading of the rule did not get far enough to say. What would settle it is reading
     * further — which is why the measure that answers this question stays open, and why the answer
     * is not that the model says nothing.
     */
    record Undetermined(BlockReason.RuleReadingStopped why) implements ObligationClassification {

        public Undetermined {
            if (why == null) {
                throw new IllegalArgumentException(
                        "a classification that did not come out says what stopped it");
            }
        }
    }
}
