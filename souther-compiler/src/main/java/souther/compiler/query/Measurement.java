package souther.compiler.query;


import java.util.Optional;

/**
 * What one measure came to: the value it made, and how far that value can be trusted.
 *
 * <p>A measurement is not a verdict. It used to be a number beside a word — {@code covered} beside
 * {@code PARTIAL} — and the word was a point on a lattice, which is by construction the join of
 * whatever was thrown away to reach it. Every producer worked out its word from a fact it then let
 * go of, and every parent worked the word out again from the fields beside its children. The fact
 * itself never had a home (issue #953).
 *
 * <p><b>This is how far asking got, and never whether there was anything to ask.</b> That question
 * is {@link Measure}'s, and a measure whose question does not exist is {@link Measure.NotApplicable}
 * rather than an arm here. So a measure that cannot fail to have a subject — the reading of a
 * behavior's rows, which has rows even where there are none — is typed as a {@code Measurement} and
 * has no applicable-or-not to answer (issue #996).
 *
 * <p><b>Four states, and the space is closed.</b> Two questions decide them — whether there is a
 * value, and whether this weakens whatever is assembled from it:
 *
 * <table>
 *   <caption>the states</caption>
 *   <tr><th>value</th><th>weakens</th><th></th></tr>
 *   <tr><td>yes</td><td>no</td><td>{@link Complete}</td></tr>
 *   <tr><td>yes</td><td>yes</td><td>{@link Partial}</td></tr>
 *   <tr><td>no</td><td>yes</td><td>{@link FailedToMeasure}</td></tr>
 *   <tr><td>no</td><td>no</td><td>{@link NotMeasured}</td></tr>
 * </table>
 *
 * <p><b>{@link FailedToMeasure} is the state that had no word.</b> A measure whose rules this
 * compiler could not read and one nobody wrote a row for were both {@code NOT_MEASURED}, and the
 * difference was recovered by asking the reason a boolean. That boolean was a fifth state hiding
 * inside a four-valued enum, and #951 put it there because there was nowhere else for it to go.
 *
 * <p><b>No value stands in for a measurement that was not made.</b> A measure with no number used to
 * be built with zeroes — an axis with {@code covered = {}} beside {@code NOT_MEASURED}, a pair space
 * with every count at zero — so "nothing was reached" and "nothing was measured" were the same
 * bytes, and a parent could reach past the status to the numbers and get an answer. The three arms
 * with no value carry none.
 *
 * <p>What every measure has in common is {@link #weakening()}, and it is the only thing anything
 * does with a measurement it did not make. There is no {@code and}: whether a parent has a value
 * when its parts do not is that parent's own question, and a single operation that answered it for
 * everybody is how the availability of a value and the completeness of a measurement came to be one
 * lattice.
 *
 * @param <T> what this measure produces where it produces anything. Only the measurement is in
 *            here — what the model says, which is true whether or not anybody measured it, stays
 *            outside beside this
 */
public sealed interface Measurement<T> extends Measure<T> {

    /**
     * What this measurement went without.
     *
     * <p>Empty for the two that weaken nothing. A parent's own weakening is the union of these
     * over its parts, and nothing else it reads.
     */
    @Override
    WeakeningSet weakening();

    /** What this measure made, where it made anything. */
    @Override
    Optional<T> made();

    @Override
    default souther.compiler.observe.MeasureReason why() {
        return switch (this) {
            case Complete<T> _, Partial<T> _ -> null;
            case NotMeasured<T> it -> it.why();
            case FailedToMeasure<T> it -> it.why();
        };
    }

    /** Everything this measure reads was readable, and this is what it found. */
    record Complete<T>(T value) implements Measurement<T> {

        public Complete {
            java.util.Objects.requireNonNull(value, "a complete measurement is of something");
        }

        @Override
        public WeakeningSet weakening() {
            return WeakeningSet.none();
        }

        @Override
        public Optional<T> made() {
            return Optional.of(value);
        }
    }

    /**
     * A value was made and something this measure reads was not readable, so a gap in it may not be
     * one.
     *
     * <p>Never weakened by nothing. A measurement that says it is weaker than complete and cannot
     * say what made it so is the whole of what this type was introduced for, and a constructor that
     * admitted an empty set would let it back in one call site at a time.
     */
    record Partial<T>(T value, WeakeningSet by) implements Measurement<T> {

        public Partial {
            java.util.Objects.requireNonNull(value, "a partial measurement is still of something");
            if (by == null || by.isEmpty()) {
                throw new IllegalArgumentException(
                        "a measurement made in part says what it was made in part by");
            }
        }

        @Override
        public WeakeningSet weakening() {
            return by;
        }

        @Override
        public Optional<T> made() {
            return Optional.of(value);
        }
    }

    /** It could have been made and nobody asked for it, so nothing was gone without. */
    record NotMeasured<T>(NotMeasuredReason why) implements Measurement<T> {

        public NotMeasured {
            java.util.Objects.requireNonNull(why, "a measure with no number says why");
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

    /**
     * It was asked for, it was started, and what it needed could not be read — so there is no value
     * and everything assembled from this is weaker for it.
     *
     * <p>Carries what it went without, exactly as {@link Partial} does, and for the same reason: the
     * reason says what kind of nothing came back, and only the weakening says what would have been
     * needed to get a number.
     */
    record FailedToMeasure<T>(FailureReason why, WeakeningSet by) implements Measurement<T> {

        public FailedToMeasure {
            java.util.Objects.requireNonNull(why, "a measure with no number says why");
            if (by == null || by.isEmpty()) {
                throw new IllegalArgumentException(
                        "a measurement that could not be finished says what it went without");
            }
        }

        @Override
        public WeakeningSet weakening() {
            return by;
        }

        @Override
        public Optional<T> made() {
            return Optional.empty();
        }
    }
}
