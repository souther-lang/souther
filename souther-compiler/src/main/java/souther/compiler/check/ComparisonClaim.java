package souther.compiler.check;

import souther.compiler.numeric.Towards;

/**
 * What a comparison placed on a position's values, read off the comparison and nothing else.
 *
 * <p>One classification, asked wherever a rule compares a position to something: a clause of an
 * invariant, a comparison in a body, a clause of an {@code ensures}. A rule is read the same way
 * wherever it is written (spec §boundary-coordinates), and this is the reading that says what it
 * placed. Answered once, and carried from wherever a comparison was recognised: a second answer to
 * it drifts from this one, and an equality places a line under one of them and nothing under the
 * other while both go on being called what a rule placed.
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
     * What the comparison that holds exactly where this one does not places, which is the same
     * partition selected the other way round.
     *
     * <p>A denial is the comparison's own meaning and not a reader's arrangement: {@code x <= c}
     * fails exactly where {@code x > c} holds, and both say the number named is on the low side.
     * Answered from the claim, a reader that meets a rule under a negation has the claim of the
     * rule it states; answered from the operator, it is a second table of operators that agrees
     * with this one only for as long as somebody keeps it so.
     *
     * <p>Asked of a claim and not of a {@link ComparisonPlacement}, because a denial is of
     * something stated. There is nothing an operator that placed nothing states the failure of.
     */
    ComparisonClaim denied();

    /**
     * An order: the values either side of the line are different classes.
     *
     * @param valueBelongs    which class the number named is itself in. {@code x <= c} puts it
     *                        below; {@code x < c} puts it above. Getting this wrong moves the line
     *                        by one and asks for a row that proves nothing
     * @param holdsAtTheValue whether the comparison is true at the number named. Not derivable
     *                        from the other: {@code x <= c} and {@code x > c} agree about which
     *                        class the number is in and disagree here
     */
    record Cut(Towards valueBelongs, boolean holdsAtTheValue) implements ComparisonClaim {

        /** Turning the sides round moves the number named to the other class and leaves whether the
         *  rule holds there alone: {@code x <= c} and {@code -x >= -c} are one statement. */
        @Override
        public Cut turned() {
            return new Cut(valueBelongs.opposite(), holdsAtTheValue);
        }

        /** The same line with the other class selected, which is what a denial of an order is. */
        @Override
        public Cut denied() {
            return new Cut(valueBelongs, !holdsAtTheValue);
        }

        /**
         * Which side of the line the comparison is true on.
         *
         * <p>The one place the two facts a cut holds are put together. Which class the number named
         * is in and whether the rule holds there are separate answers, and every question about the
         * line — which end of a range it is, which way a run of values has to lie to satisfy it,
         * which side a row is owed on — is this one. Worked out where each of those is asked, the
         * pairing of the two is remembered in as many places as there are readers, and the two
         * facts are of one type, so a reader that pairs them the other way round is a reader
         * nothing contradicts.
         */
        public Towards satisfyingSide() {
            return holdsAtTheValue ? valueBelongs : valueBelongs.opposite();
        }

        /**
         * The order satisfied on {@code side} that answers {@code holdsAtTheValue} at the value it
         * names, which is {@link #satisfyingSide} read the other way.
         *
         * <p>For a reader that kept the side rather than the class the value is in — a bound
         * records which end of a range it placed, and which side its own value falls on follows
         * from that end together with whether the bound admits it. Run backwards by such a reader,
         * the derivation is the pairing of the two facts written a second time, and a line stated
         * as one end and read back as the other is a line whose sides are the wrong way round.
         */
        public static Cut satisfiedOn(Towards side, boolean holdsAtTheValue) {
            return new Cut(holdsAtTheValue ? side : side.opposite(), holdsAtTheValue);
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
        public Singled turned() {
            return this;
        }

        /** The other of the two classes: what is denied of the value named is met everywhere
         *  else. */
        @Override
        public Singled denied() {
            return new Singled(!holdsAtTheValue);
        }
    }

}
