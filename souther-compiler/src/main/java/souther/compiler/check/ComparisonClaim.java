package souther.compiler.check;

/**
 * What a comparison placed on a position's values, read off the comparison and nothing else.
 *
 * <p>One classification, asked wherever a rule compares a position to something: a clause of an
 * invariant, a comparison in a body, a clause of an {@code ensures}. A rule is read the same way
 * wherever it is written (spec §boundary-coordinates), and this is the reading that says what it
 * placed. It was three: {@code InvariantBound.ordering} answered it for a {@code data}'s clauses,
 * {@code ComparedLine.of} for a body's and a declaration's comparisons, and
 * {@code GuardThresholds.orders} answered a coarser version of the same question under the same
 * word. Three answers to one question drift, and two of them already had: an equality places a line
 * where a body writes it and placed nothing where a {@code data} did.
 *
 * <p><b>Two cases, because an operator that placed nothing is no comparison.</b> That an operator
 * compares is settled where a comparison is recognised ({@link Comparison}), and this is what such
 * an operator placed — so there is no arm here for one that placed nothing, and no reader below
 * that point has one to answer for. Held as the wider {@link ComparisonPlacement}, every one of
 * them did, and what each answered was invented: a {@code null} for a relation that does not exist,
 * a {@code false} for a rule that holds at no value because there is no rule.
 *
 * <p><b>And nothing about which values exist.</b> Whether there is anything on the far side of the
 * line is not the comparison's to say: an invariant refuses everything outside its bound at
 * construction, and a {@code guard} comparing the same number leaves values on both sides. That is a
 * fact about the construct the rule is written in, asked beside this rather than inside it — read as
 * one question, a guard's classification would carry an invariant's reason.
 */
public sealed interface ComparisonClaim
        extends ComparisonPlacement permits ComparisonClaim.Cut, ComparisonClaim.Singled {

    /**
     * Whether the comparison is true at the value it names.
     *
     * <p>Asked of either shape, because either answers it: {@code x <= c} and {@code x > c} agree
     * about which class the value is in and disagree here, and {@code x == c} is met at the value
     * where {@code x /= c} is not.
     */
    boolean holdsAtTheValue();

    @Override
    ComparisonClaim turned();

    /**
     * An order: the values either side of the line are different classes.
     *
     * @param valueBelongsBelow whether the number named is on the low side. {@code x <= c} puts it
     *                          there; {@code x < c} puts it on the high side. Getting this wrong
     *                          moves the line by one and asks for a row that proves nothing
     * @param holdsAtTheValue   whether the comparison is true at the number named. Not derivable
     *                          from the other: {@code x <= c} and {@code x > c} agree about which
     *                          class the number is in and disagree here
     */
    record Cut(boolean valueBelongsBelow, boolean holdsAtTheValue) implements ComparisonClaim {

        /** Turning the sides round moves the number named to the other class and leaves whether the
         *  rule holds there alone: {@code x <= c} and {@code -x >= -c} are one statement. */
        @Override
        public ComparisonClaim turned() {
            return new Cut(!valueBelongsBelow, holdsAtTheValue);
        }
    }

    /**
     * A value singled out: the number named, and every other value as one class.
     *
     * <p>{@code x == c} and {@code x /= c} place the same thing. What they distinguish is the value
     * from every other value, and which of the two classes the comparison selects is
     * {@code holdsAtTheValue}, not a different partition — so reading either as a place to cut would
     * put an order between the two sides that the model never drew.
     *
     * <p>Which side is writable is the construct's answer and not this one. Under an invariant the
     * value singled out is admitted where the comparison holds at it and refused where it does not,
     * and a refused one leaves a hole rather than an edge: the values beside it are on both sides,
     * which is not what a boundary with a low side and a high side can carry.
     */
    record Singled(boolean holdsAtTheValue) implements ComparisonClaim {

        /** An equality names a value and orders nothing, so there is nothing to turn round. */
        @Override
        public ComparisonClaim turned() {
            return this;
        }
    }

}
