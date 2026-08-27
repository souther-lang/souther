package souther.compiler.partition;

/**
 * A condition on the way to a border that a row for it was not composed against, and which stage
 * let it go.
 *
 * <p><b>Two stages, and a condition belongs to one of them at a time.</b> {@link OnTheWay} is the
 * walk's classification: a condition either landed in a vocabulary — the arithmetic's or the
 * positions' — or the walk had no words for it. A condition that landed and that the composer could
 * not then put a value under has not stopped being a cut, and saying so by writing it down a second
 * time as a decline would be one condition wearing two of the walk's answers.
 *
 * <p>So the walk's answer is kept and the stage is what this adds. What a reader of a point wants is
 * one list — everything the row it was offered, or not offered, was composed without — and which of
 * these each entry is says what would change it: a word this reading does not have, or a value this
 * composer cannot build.
 */
public sealed interface ReachabilityGap {

    /** Where the condition is, as a report is entitled to say it. */
    souther.compiler.diag.Citation at();

    /** The walk had no words for it, so nothing downstream ever saw it. */
    record Unstated(OnTheWay.Declined condition) implements ReachabilityGap {

        @Override
        public souther.compiler.diag.Citation at() {
            return condition.at();
        }
    }

    /**
     * The walk stated it and nothing composed a value under it.
     *
     * <p>Carrying the cut and not a copy of what it said. The condition is the same one the walk
     * took in — a report may say which positions it is over, and a reader asking why the row does
     * not meet it is asking about that cut — so what is added here is the stage and the reason, and
     * the condition keeps the identity it was given.
     */
    record Uncomposed(OnTheWay.TakenIn condition, Why why) implements ReachabilityGap {

        @Override
        public souther.compiler.diag.Citation at() {
            return condition.at();
        }
    }

    /**
     * What stopped a stated condition from being composed against.
     *
     * <p>Each says what this composer did rather than what the model says. A row is written without
     * the condition either way, so nothing read off one of these says the condition cannot be met —
     * and a word going away is a capability gained.
     */
    sealed interface Why {

        /**
         * No value was composed at some position the condition is over.
         *
         * <p>Said of the whole condition, because a cut over two positions is one statement about
         * the pair. One of them put where the cut admits and the other left to its own declared
         * range is not half the condition holding — it is the condition not holding, with a
         * position pinned on the strength of it. So a condition this cannot place every position of
         * is placed at none of them.
         */
        record NoValueComposedForItsPositions() implements Why {}

        /**
         * Two numbers taken at one location, one of which the row is already being written for.
         *
         * <p>A row writes one value where a location is, and that one value would have to answer
         * both — the length of a string beside the string. Told apart from the one above because
         * only this one is about the condition and the item meeting at a location rather than about
         * what could be built at a position.
         */
        record TwoNumbersAtOneLocation() implements Why {}
    }
}
