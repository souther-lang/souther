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
 * <p><b>Asked for every question and at every place, and answered by a switch with no
 * {@code default}.</b> A question added to {@link CoverageObligation} is one this has to be given
 * an answer for at each shape a clause can be read into; left out, it would arrive as "does not
 * raise it" at every place, and a measure would be complete over a model nobody had classified.
 */
sealed interface Presence {

    /** The rule raises it, and this is the question. */
    record Raised(Owed owed) implements Presence {

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
    record NotRaised() implements Presence {}

    /**
     * Nothing worked out whether it raises it.
     *
     * <p>The reading of the rule did not get far enough to say. What would settle it is reading
     * further — which is why the measure that answers this question stays open, and why the answer
     * is not that the model says nothing.
     */
    record Undetermined(BlockReason.RuleReadingStopped why) implements Presence {

        public Undetermined {
            if (why == null) {
                throw new IllegalArgumentException(
                        "a classification that did not come out says what stopped it");
            }
        }
    }
}
