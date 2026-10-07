package souther.compiler.partition;

import souther.compiler.types.ModelOccurrence;

/**
 * What a run down one path of a body would be seen doing, for one condition of it.
 *
 * <p>Beside a rule and not inside it. A rule is told apart by the distinctions it consulted, and
 * where a run through one of them is written down is not one of them — two bodies stating one rule
 * in two places state one rule. What this is for is the other direction: a reader holding a run
 * asks which rule it took, and these are what it asks about.
 *
 * <p>Said in the model's words. Which construct of the model a condition is is what the tree the
 * rules are read off and the tree that runs agree about; where the emitter numbered it is that
 * construct looked up in a plan, and is the plan's answer rather than this one's.
 *
 * <p><b>And where there is nothing to be seen, that.</b> A condition this reading has no words for
 * is a condition it cannot name a construct of the model for either, so a rule carrying one is a
 * rule no run can be shown to have taken. Left off, such a rule would look witnessed by whichever
 * conditions beside it were seen.
 */
public sealed interface ShownBy {

    /**
     * A construct of the model answering a truth one way: a comparison, or an application of one
     * of the language's operations.
     *
     * <p>One shape for the two. What a run records of either is the truth it answered where it
     * answered it, and which kind of construct gave that truth is the construct's to say — a
     * reader of the place a run is seen at that asked would be telling two places apart that are
     * recorded alike.
     *
     * @param construct which construct of the model
     * @param held      the way the path took it
     */
    record AtAnOutcome(ModelOccurrence construct, boolean held) implements ShownBy {

        public AtAnOutcome {
            if (construct == null) {
                throw new IllegalArgumentException("a truth of the model is some construct's");
            }
        }
    }

    /**
     * One arm of a fork of the model.
     *
     * <p>The arm and not the narrowing it establishes. What a run writes down is which way it went;
     * what the rule says the value turned out to be is the column, and the two are answers to one
     * question in two vocabularies.
     */
    record AtAnArm(ModelOccurrence fork, int part) implements ShownBy {

        public AtAnArm {
            if (fork == null) {
                throw new IllegalArgumentException("an arm is an arm of some fork of the model");
            }
            if (part < 0) {
                throw new IllegalArgumentException("an arm stands somewhere among its fork's: "
                        + part);
            }
        }
    }

    /**
     * One arm of a fork, taken without the operand {@code notReached} having run.
     *
     * <p>For a condition settled on the left of an operator that stops when its answer is settled,
     * which no construct records: what a run shows of it is that the right was not run. That is
     * only an answer where the operator was run at all, and taking the arm of a fork whose
     * condition runs the operator first is what says it was — so the two are one place to be seen
     * at, and neither is one alone.
     *
     * @param fork       which fork of the model
     * @param part       which arm of it
     * @param notReached the right operand, as the construct of the model a run through it is
     *                   recorded at
     */
    record AtAnArmShortOf(ModelOccurrence fork, int part, ModelOccurrence notReached)
            implements ShownBy {

        public AtAnArmShortOf {
            if (fork == null || notReached == null) {
                throw new IllegalArgumentException("an arm taken short of an operand is an arm of"
                        + " some fork and short of some construct");
            }
            if (part < 0) {
                throw new IllegalArgumentException("an arm stands somewhere among its fork's: "
                        + part);
            }
        }
    }

    /**
     * A condition nothing records, settled on the left of an operator whose right was not run.
     *
     * <p>Not yet a place to be seen at. That the right did not run says the left settled only where
     * the operator ran, which an arm of the fork it decides says ({@link AtAnArmShortOf}); until a
     * fork says so this is a condition no run is recognised through, as {@link NothingIsRecorded}
     * is.
     *
     * @param condition  the column, which tells two of these apart
     * @param notReached the right operand that was not run
     */
    record ShortOf(DecisionCondition condition, ModelOccurrence notReached) implements ShownBy {

        public ShortOf {
            if (condition == null || notReached == null) {
                throw new IllegalArgumentException(
                        "a condition settled short of an operand is some condition, short of some"
                                + " construct");
            }
        }
    }

    /**
     * A condition with no construct of the model to be seen at.
     *
     * <p>Named by the column, which is what tells two of them apart wherever anything does. What a
     * rule carrying one says is that a run through it cannot be recognised, which is this
     * compiler's shortfall rather than anything about the model.
     *
     * <p>A truth the body asks of a name it was handed, or of a value no construct of the model
     * answers, is one of these: there is no construct for a run to have answered it at. Except
     * where the fork it is asked by is entered by that one way alone, and then the arm a run takes
     * is where it is seen ({@link AtAnArm}).
     */
    record NothingIsRecorded(DecisionCondition condition) implements ShownBy {

        public NothingIsRecorded {
            if (condition == null) {
                throw new IllegalArgumentException(
                        "a condition nothing records is some condition");
            }
        }
    }
}
