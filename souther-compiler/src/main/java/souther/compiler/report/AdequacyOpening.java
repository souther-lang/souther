package souther.compiler.report;

import souther.compiler.observe.RunSensitivity;
import souther.compiler.query.NotMeasuredReason;
import souther.compiler.query.Weakening;

/**
 * One thing keeping an adequacy verdict undetermined.
 *
 * <p>Not a {@link Weakening}, and that is the whole of why this type exists. A verdict is settled
 * by every measure it rests on having come to an answer nothing weakened, so it is held open by two
 * different things: a measure that was made and went without something, and a measure that could
 * have found a gap and was never made. The second weakens nothing — {@link
 * souther.compiler.query.Measurement.NotMeasured} carries no {@code WeakeningSet} on purpose, which
 * is what separates it from a measurement that was asked for and could not be finished — so a list
 * of weakenings said nothing at all about a model nobody has written rows for, while the verdict
 * over it was open.
 *
 * <p>Read off the verdict's own predicate rather than assembled beside it. Every arm below is what
 * one of the things {@code adequacy()} walks contributes, so {@code undetermined} and this being
 * empty cannot both be true — which is a property worth having and is the one the conformance
 * corpus produced a counterexample to.
 *
 * <p><b>What it is not.</b> Not everything that left the report weaker than it looks: a measure
 * this build is not held to may be as partial as it likes without a bar being any less settled by
 * it. And not a second vocabulary — each arm is projected to a word the document already has.
 */
public sealed interface AdequacyOpening {

    /** Whether a run of this compiler that allows more could get past this. */
    RunSensitivity runSensitivity();

    /**
     * A measure was made and went without something.
     *
     * <p>One per fact, and the facts have already been folded: two measures that went without the
     * same thing went without one thing, which is {@code WeakeningSet}'s. Nothing folds them again
     * on what they are printed as — two rules this compiler could not read are two of these, and a
     * document calls them by one word.
     */
    record ByWeakening(Weakening cause) implements AdequacyOpening {

        public ByWeakening {
            if (cause == null) {
                throw new IllegalArgumentException("a verdict held open by nothing is settled");
            }
        }

        @Override
        public RunSensitivity runSensitivity() {
            return cause.runSensitivity();
        }
    }

    /**
     * A measure the verdict rests on was never made, and this is what it says about that.
     *
     * <p>One per measure and never folded on the reason. Two measures that were both waiting on
     * rows are two measures nobody made, and a set keyed on {@code no_rows} would say a model with
     * one behavior unmeasured and a model with forty were the same news.
     *
     * <p>{@link RunSensitivity#UNAFFECTED}, and the word means what it says rather than what a
     * reader might hope. Widening an allowance does not make a measurement nobody asked for; what
     * does is a row, and a row is a change to the model rather than a wider run of this compiler
     * over it. What a person may go on to do is the reason's, which is why it travels.
     */
    record NotMeasured(NotMeasuredReason why) implements AdequacyOpening {

        public NotMeasured {
            if (why == null) {
                throw new IllegalArgumentException("a measure nobody made says why");
            }
        }

        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }
}
