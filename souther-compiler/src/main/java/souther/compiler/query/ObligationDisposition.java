package souther.compiler.query;

import java.util.Collections;
import java.util.EnumSet;
import java.util.Set;

/**
 * What became of one obligation the model owes a row at.
 *
 * <p>Derived from the evidence and never held beside it. What the readings came to
 * ({@link ObligationCoverage}) and what has shown a row can be written here
 * ({@link ItemAssessment.WritabilityEvidence}) are answers to two questions, and this is the one
 * question a count, a finding and a build's refusal all put: is this row written, owed, or neither.
 * Asked of the evidence at each of those places instead, the three had three chances to read one
 * pair of answers differently.
 *
 * <p><b>Three states, and every one of them is counted.</b> Whether a row is owed at a point is the
 * model's answer and is settled before anything here: a border that owes no row at a point says so
 * with a reason read off the rules ({@link souther.compiler.partition.NotOwedReason}), and a point
 * the rules leave nothing at never becomes an obligation. Nothing this compiler failed to read,
 * compose or represent reaches that decision, so nothing here subtracts. What the three say is what
 * is known about a point that is owed: a row stands at it, no row does and something showed one
 * could, or nobody can say which.
 *
 * <p>There was a fourth. A point every row was read against and none was at, with nothing to show a
 * row could be written there, was left out of the account entirely — on the reading that asking for
 * a row nothing promises is asking for work nobody can do. That reads a limit of this compiler as an
 * answer about the model. Nothing composed and every candidate refused are facts about the composer;
 * the model's own refusal has its own way of being said, two paragraphs up, and is not any of them.
 * What the fourth state cost is that a field nobody could compose a value for took its siblings'
 * obligations out of the denominator with it — the row is written against the whole value, so one
 * unreadable rule anywhere under a parameter emptied the grounds for every point beneath it
 * (issue #1249).
 */
public sealed interface ObligationDisposition {

    /** A row this compilation observed stands at the point. */
    record Met() implements ObligationDisposition {}

    /**
     * No row is at the point, the readings ran to the end, and something has shown a row can be
     * written there. The one state a finding is made of and a build can be told to refuse over.
     */
    record Unmet() implements ObligationDisposition {}

    /**
     * No row was seen, and something this compiler could not do is why nobody can say more.
     *
     * <p>Counted and never a finding. Whether a row is at the point is what nobody can say, so an
     * author told to write one may be told to write one they have written, or one this compiler
     * cannot show exists. The obligation stands all the same: it is what the model owes, and what
     * nobody could establish about it is news about this compiler rather than a discharge.
     *
     * <p><b>Two questions can be the one nobody can answer, and they are told apart.</b> Nothing
     * settled whether a row that is written stands here; or the rows were read to the end and it was
     * the showing that a row can be written here that came to nothing. Both leave the point
     * undecided and they leave different work: the first is answered by reading rows, the second by
     * this compiler being able to compose, keep or represent more than it does. Held as one state, a
     * reader is told a verdict and left to work out which question it is about — from the verdict,
     * which is the one thing that does not say.
     *
     * <p>A set, because one obligation can be both, and either one alone would be a choice of which
     * to tell.
     */
    record Undecided(Set<Uncertainty> because) implements ObligationDisposition {

        public Undecided {
            if (because == null || because.isEmpty()) {
                throw new IllegalArgumentException(
                        "an obligation nobody can decide says which question is open");
            }
            because = Collections.unmodifiableSet(EnumSet.copyOf(because));
        }
    }

    /** Which question about an obligation is the one nothing answered. */
    enum Uncertainty {
        /**
         * Whether a row that is written stands at the point.
         *
         * <p>A reading that stopped short, or no reading at all. Which of the two it was is the
         * coverage's own to say ({@link ObligationCoverage.Undecided} carries what its readings went
         * without, {@link ObligationCoverage.NotMeasured} carries why nobody looked), and a second
         * word for it here would be this reading of the pair deciding what the coverage already
         * answered.
         */
        COVERAGE,
        /**
         * Whether a row can be written at the point.
         *
         * <p>The showing came to nothing, whether it was stopped on the way
         * ({@link WritabilityKnowledge.Prevented}, which says what stopped it) or composed nothing
         * to be stopped ({@link WritabilityKnowledge.NoEvidence}). Neither is the model saying a row
         * cannot stand here.
         */
        WRITABILITY
    }

    /**
     * Where {@code coverage} and {@code knowledge} put the obligation.
     *
     * <p>The one place the pair is read, and read coverage first. What the rows came to is what
     * decides which question is even open: a row found is met whatever else is so, and a reading
     * that came to nothing leaves the point undecided whatever anybody built.
     *
     * <p><b>What has shown a row can be written is a refinement of one of those and not a gate over
     * all of them.</b> It is what tells a miss the rows ran out on from a finding — an author told
     * to write a row at a point nothing promises may be told to write one this compiler cannot show
     * exists. What it never does is decide whether the point is owed. Asked before the coverage
     * instead, it answered a question about the model with what this compiler managed to build.
     */
    static ObligationDisposition of(ObligationCoverage coverage, WritabilityKnowledge knowledge) {
        return switch (coverage) {
            case ObligationCoverage.Witnessed _ -> new Met();
            // What the rows left open, and beside it whatever else is open about the same point. A
            // reading that came to nothing and a showing that came to nothing are two questions, and
            // a point where both happened is undecided about both. The same holds where nothing was
            // read at all: which of the two the coverage was is the coverage's to say, and both
            // leave whether a row stands here unanswered.
            case ObligationCoverage.Undecided _, ObligationCoverage.NotMeasured _ -> {
                Set<Uncertainty> open = EnumSet.of(Uncertainty.COVERAGE);
                if (!(knowledge instanceof WritabilityKnowledge.Established)) {
                    open.add(Uncertainty.WRITABILITY);
                }
                yield new Undecided(open);
            }
            case ObligationCoverage.Missed _ -> switch (knowledge) {
                case WritabilityKnowledge.Established _ -> new Unmet();
                // The rows are read out and no row is at the point, and what would have shown a row
                // can be written did not arrive. No finding is made of it, because nothing here can
                // say the row an author would write is one that exists — and the obligation stays,
                // because what did not arrive is a showing and not the model's answer.
                case WritabilityKnowledge.Prevented _, WritabilityKnowledge.NoEvidence _ ->
                        new Undecided(EnumSet.of(Uncertainty.WRITABILITY));
            };
        };
    }
}
