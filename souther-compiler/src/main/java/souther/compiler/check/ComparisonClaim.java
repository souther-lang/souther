package souther.compiler.check;

import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.numeric.Towards;

import java.util.Objects;

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

    /**
     * The relation this states of its two sides, which is what the numeric reasoning is written in.
     *
     * <p>The one crossing between the two vocabularies, and it is a crossing rather than a second
     * name for one thing. What is here says how a comparison divided a position's values, and
     * answers which class the number named is in and which side the rule is satisfied on; a
     * relation says which way a sum stands to nought, and is what a domain is told and what a bound
     * arriving from somewhere no comparison was written is also said in. The six of each line up,
     * so nothing is lost crossing over — and that they line up is why it is written once here
     * rather than wherever a reader happens to need the other words.
     *
     * <p>Stated of the left side against the right, which is the way round every reader of a
     * relation reads it ({@link Rel#holds}).
     */
    Rel statedRelation();

    /**
     * The canonical statement this claim makes of {@code left} and {@code right}.
     *
     * <p>The one derivation from what a comparison placed to what it states. Two facts decide it
     * and neither decides the other: which class the value named is in says which side of the
     * canonical order each of the two goes on, and whether the comparison holds at the value says
     * whether the canonical statement is denied. The two shapes read the second fact opposite ways,
     * because an order does not hold at the value it names and an equality does.
     *
     * <p>Here rather than wherever a reader wants it, because a reader that pairs the two facts
     * itself remembers the pairing in as many places as there are readers, and one that pairs them
     * the other way round states the comparison that holds exactly where this one does not while
     * answering every one of its own questions consistently.
     */
    <A> CanonicalComparison<A> canonical(A left, A right);

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

        /**
         * A side and not the absence of one.
         *
         * <p>Which class the number named is in is one of two answers and the language has no way
         * to say so of a reference, so it is said here. Absent, every reader comparing it to a
         * side gets the other one — a cut with no side reads as one bounding the values below, and
         * an order the model never stated goes on being answered about.
         */
        public Cut {
            Objects.requireNonNull(valueBelongs, "which class the number a cut names is in");
        }

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

        /** The canonical order, taken with the value named above the other — which is the side the
         *  canonical form wants it on, so a cut that puts it below states the same thing with its
         *  sides exchanged — and denied where the comparison holds at the value, because the
         *  canonical order does not hold there. */
        @Override
        public <A> CanonicalComparison<A> canonical(A left, A right) {
            boolean exchanged = valueBelongs == Towards.BELOW;
            CanonicalComparison<A> order = CanonicalComparison.below(
                    exchanged ? right : left, exchanged ? left : right);
            return holdsAtTheValue ? order.denied() : order;
        }

        /** Which way the values it admits lie, and whether the number named is one of them: the
         *  side is the claim's own answer ({@link #satisfyingSide}) and is not worked out here from
         *  the two facts a cut holds. */
        @Override
        public Rel statedRelation() {
            return satisfyingSide() == Towards.BELOW
                    ? (holdsAtTheValue ? Rel.LE : Rel.LT)
                    : (holdsAtTheValue ? Rel.GE : Rel.GT);
        }

        /**
         * Which side of the line the comparison is true on.
         *
         * <p>The one place the two facts a cut holds are put together. Which class the number named
         * is in and whether the rule holds there are separate answers, and every question about the
         * line — which end of a range it is, which way a run of values has to lie to satisfy it,
         * which side a row is owed on — is this one. Worked out where each of those is asked, the
         * pairing of the two is remembered in as many places as there are readers, and a reader
         * that pairs them the other way round answers every one of its own questions consistently
         * about a line whose sides are swapped.
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

        /** The two sides being the same value, denied where the comparison does not hold at the
         *  value it names — which is the canonical equality read the way round it is stated, and
         *  the opposite of how an order reads that same fact. Nothing is exchanged: an equality
         *  orders nothing, so neither side is the one the canonical form wants. */
        @Override
        public <A> CanonicalComparison<A> canonical(A left, A right) {
            CanonicalComparison<A> equality = CanonicalComparison.theSameValue(left, right);
            return holdsAtTheValue ? equality : equality.denied();
        }

        /** An equality or its denial, which is the whole of what singling a value out states. */
        @Override
        public Rel statedRelation() {
            return holdsAtTheValue ? Rel.EQ : Rel.NE;
        }
    }

}
