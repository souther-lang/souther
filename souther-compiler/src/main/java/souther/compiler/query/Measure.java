package souther.compiler.query;

import souther.compiler.observe.MeasureReason;
import souther.compiler.observe.NotApplicableReason;

import java.util.Objects;
import java.util.Optional;

/**
 * One measure, asked of one thing: whether there is a question here at all, and where there is, what
 * asking it came to.
 *
 * <p><b>Two questions, and only the second is about measuring.</b> {@link NotApplicable} says there
 * is nothing here for this measure to be about — a behavior with no body has no arms to count, a
 * signature with no sum anywhere in it has no cases to witness — and no row anybody could write
 * would change that. {@link Measurement} is what asking a question that does exist came to.
 *
 * <p>These were one sum with five arms, and the arms were right. What was wrong is that they answer
 * two different questions, and a type that holds both forces every measure to have an applicability
 * whether or not the question means anything for it. Issue #996 is what that costs: the reading of a
 * behavior's rows is a measure that is <em>always</em> applicable — a behavior has rows, even zero of
 * them — and there was no way to say so, so a module every domain measure of which was
 * {@code NotApplicable} had nowhere to put what its run went without, and reported {@code complete}
 * beside a line saying a row of it did not come back.
 *
 * <p>The vocabulary had already crossed this line. A measure with no number answers {@link #why()}
 * with one of three reason types — {@code NotApplicableReason}, {@code NotMeasuredReason},
 * {@code FailureReason} — so the reasons knew that applicability and progress are different
 * questions while the states did not.
 *
 * <p><b>What a producer may introduce {@link NotApplicable} from.</b> Only a reading of the model
 * that ran to the end and found no subject. Never the absence of something derived from the model:
 * a body that was not lowered, a plan that did not come back, a table nothing filled in. Those are
 * a measure that was started and could not be finished, which is {@code FailedToMeasure} and says
 * what it went without. The difference is the whole of what this arm asserts, and a producer that
 * reads an empty collection as a proof of absence is making the assertion without the proof.
 *
 * @param <T> what this measure produces where it produces anything
 */
public sealed interface Measure<T> permits Measurement, Measure.NotApplicable {

    /**
     * What this measure went without.
     *
     * <p>Empty wherever nothing was gone without, and that includes {@link NotApplicable}: a
     * question that does not exist cannot be short of an answer. A parent's own weakening is the
     * union of these over its parts, and nothing else it reads.
     */
    WeakeningSet weakening();

    /** What this measure made, where it made anything. */
    Optional<T> made();

    /**
     * Why there is no value, or null where there is one.
     *
     * <p>Which of the kinds of no-value it is, is the reason's own type. This is not a status in
     * disguise: it answers what a measure could not do and never how far a document should say it
     * got, which is {@code souther.compiler.report}'s and is made there once.
     */
    MeasureReason why();

    /**
     * There is nothing here for the measure to be about, and no row would change that.
     *
     * <p>A positive claim about the model, and the strongest thing anything here says. It is not
     * "nothing came back" and not "nobody asked": it is that the model was read to the end and holds
     * no subject for this measure. Read the class javadoc before writing a new producer of one.
     */
    record NotApplicable<T>(NotApplicableReason why) implements Measure<T> {

        public NotApplicable {
            Objects.requireNonNull(why, "a measure with no number says why");
        }

        @Override
        public WeakeningSet weakening() {
            return WeakeningSet.none();
        }

        @Override
        public Optional<T> made() {
            return Optional.empty();
        }
    }
}
