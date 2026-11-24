package souther.compiler.partition;

import souther.compiler.check.AffineForms;

/**
 * Which answers about a name are kept for another reading to take
 * ({@link souther.compiler.check.ValueStanding.Names#answerOfAName}).
 *
 * <p>An answer is kept only where taking it again would be working it out again. A reading that
 * charged a figure of this compiler's work was charged for what it did, and the one that takes the
 * answer is not. A reading that asked a figure anything, answered or refused, is the answer of the
 * figure's state then: a refusal adds nothing to what the figure counts, and is followed by the
 * rules that read what it refused another way. A stop at a figure is a fact of the work done.
 */
final class KeptAnswers {

    private KeptAnswers() {}

    /**
     * Whether an answer may be kept.
     *
     * @param chargedNothing   whether the reading took nothing from the readings still allowed
     * @param figureAskedBefore how many times the figure counting elements had been asked of
     *                          when the reading began
     * @param figureAskedAfter  and when it ended
     * @param answer            what it came to
     */
    static boolean keepable(boolean chargedNothing, int figureAskedBefore, int figureAskedAfter,
                            Object answer) {
        return chargedNothing && figureAskedBefore == figureAskedAfter
                && !(answer instanceof AffineForms.Outcome.StoppedAt<?, ?> stop
                && stop.why().declinedFigure().isPresent());
    }
}
