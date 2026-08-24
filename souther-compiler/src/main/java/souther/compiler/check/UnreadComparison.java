package souther.compiler.check;

import souther.compiler.inputs.BlockReason;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Why a comparison naming a position did not become a line.
 *
 * <p>One rule, asked by every reader that has to say so. A {@code guard}'s comparison and an
 * invariant's clause are two producers of one kind of evidence (spec §example-partition), and what
 * stopped each of them is the same fact about this compiler — so a reader of either is told the
 * same thing (ADR-0090). Written twice, the two came apart at once: {@code x < y + 1} was a
 * comparison between two positions where a body wrote it and a form nobody could read where a
 * declaration did, which sends an author after two different pieces of work for one shape.
 *
 * <p>How a position is looked up stays with each reader, exactly as it does in {@link Relates}. One
 * asks what a body's read of a parameter names, the other asks what a clause's coordinate is
 * called; neither is the other's business. What is here is what the answers come to, which is the
 * part that has to agree.
 *
 * <p><b>Every answer is read off what the comparison is, and none off what a reader could not
 * do.</b> The arithmetic says whether it read a quantity and what that quantity is over; it does
 * not say so by declining to answer. An expression that stopped one reader is described by what it
 * is made of ({@link ValueOrigin}) — an operation's answer is not a syntax nobody reads, and told
 * that, an author goes looking for a spelling that was never the difficulty.
 *
 * <p>What a position is called travels with the answers and is never read here, only compared with
 * another of its own. So the readers may hold a position under whatever name each of them uses and
 * still be held to one rule.
 */
public final class UnreadComparison {

    /**
     * What the arithmetic made of the comparison.
     *
     * <p>Three cases and not a set that may be absent. That the arithmetic read no form at all is an
     * answer about the comparison, and holding it as a missing set made it an answer about the
     * reader — after which the word a report printed turned on which side of the affine fragment an
     * operation happened to fall, which is no fact about the rule.
     *
     * <p><b>Each of them carries what it stands for.</b> A quantity over nothing is not a quantity,
     * and a reading that stopped is not one without somewhere it stopped — held as cases that can be
     * made from nothing, one of them stands in for another and whoever reads it reconstructs the
     * difference from whatever else is to hand.
     */
    public sealed interface Quantity<K> {

        /** The positions the quantity this comparison cuts is over. */
        record Over<K>(Set<K> positions) implements Quantity<K> {

            public Over {
                positions = java.util.Collections.unmodifiableSet(new LinkedHashSet<>(positions));
                if (positions.isEmpty()) {
                    // A quantity over no position is what {@link CutsNothing} says, and saying it
                    // twice lets a reader answer one of them for the other.
                    throw new IllegalArgumentException(
                            "a quantity is over something; nothing cut is CutsNothing");
                }
            }
        }

        /**
         * The arithmetic read the whole comparison and there is no quantity to cut: a comparison of
         * constants, or one whose positions cancel.
         *
         * <p>Its own answer and not the one below. {@code a - a > 0} is read to the end and divides
         * no position, which is a fact about the rule; folded together with a reading that stopped,
         * it was reported as a rule written in a form this compiler cannot read — of a form this
         * compiler read completely.
         */
        record CutsNothing<K>() implements Quantity<K> {}

        /**
         * The arithmetic read no form here, and what it was looking at when it stopped.
         *
         * <p>The expression, because the walk that stopped is the only thing that knows which one it
         * was. Told only that there was no form, a reader had to work the difficulty out from the
         * shape of the whole comparison, and the shape it reached for first was whichever side held
         * an operation — so a rule over an operation this reads perfectly well was blamed for a form
         * it could not read beside it, and would go on being blamed as more operations became
         * readable.
         *
         * @param stoppedAt what the expression with no rule here is made of
         */
        record NotRead<K>(ValueOrigin<K> stoppedAt) implements Quantity<K> {

            public NotRead {
                if (stoppedAt == null) {
                    throw new IllegalArgumentException(
                            "a reading that read no form stopped somewhere");
                }
            }
        }
    }

    /**
     * What would have to change before this comparison could be a line.
     *
     * <p>Four different things, and a reader told one sentence for all of them cannot tell which
     * limit is theirs to wait on. A comparison between two positions asks for a class that is about
     * both, which a partition of one position is not. One on a carrier nothing draws a line on asks
     * for that carrier. One written about what an operation answered asks for a statement about
     * that operation. What is left is a form this does not read — the position inside arithmetic the
     * terms do not take apart, or a threshold written as something other than a constant.
     *
     * <p>Two positions is asked of what the sides <em>name</em>, however deeply, and not of what
     * they are. That is as true of {@code x < y + 1} as of {@code x < y}: reading it off whether a
     * side is a position loses the second position entirely and answers with the form.
     *
     * <p>And of <em>another</em> position, not of a position on each side ({@link Relates}).
     * {@code x < x + 1} has a position on both sides and one position, so there is no second one
     * for a class to be about — what a reader would have to be given is a reading of the form, and
     * being sent after a relation sends them looking for a position the model never wrote.
     *
     * <p><b>Asked of what the rule cuts, and of the sides only where that is unreadable.</b> Which
     * side a position is written on is no part of whether a rule relates two of them: {@code 3 * a +
     * 6 * b <= 48} puts both on one side and divides neither. What says so is the quantity the
     * canonical form cuts, which each reader works out with its own atoms and its own environment —
     * the same division of labour {@link ValueOrigin} already has. Where the arithmetic reads
     * nothing there is no quantity to count, and the sides answer: {@code a > b} over strings
     * relates two positions on an order with no numbers, and {@code a * b > 5} names two and is
     * stopped by neither of them.
     *
     * @param ordered whether a line can be drawn on what a position carries, asked of the carrier.
     *                Asked of the reader because a position is looked up there, and asked at all
     *                only about a side that is one
     */
    public static <K> BlockReason.AboutARule why(ValueOrigin<K> left, ValueOrigin<K> right,
                                                 Quantity<K> quantity, Predicate<K> ordered) {
        // What the rule cuts, where the arithmetic could be read at all. A quantity over
        // more than one position divides none of them — which values of one are on which
        // side depends on the others — and that is as true of `3a + 6b <= 48`, whose two
        // sit on one side, as of `a < b`. Counted off the sides instead, the first came
        // back as a form nobody could read; counted off how many positions the comparison
        // names, `a * b > 5` came back as a relation when what stops it is the product.
        return switch (quantity) {
            // Read to the end and there is no quantity. Nothing about how it was written adds to
            // that: no reading fell short, so no question about what could not be read arises.
            case Quantity.CutsNothing<K> _ -> new BlockReason.ComparisonCuttingNothing();
            // Over one position, that one is what the rule divides however many the spelling
            // mentions: `a + b > b` cuts `a`, and counted off the sides it was a relation the model
            // does not state.
            case Quantity.Over<K> over -> over.positions().size() > 1
                    ? new BlockReason.ComparisonBetweenPositions()
                    : whatThisSideSays(speakingSide(left, right), ordered);
            // No quantity was read, so what the sides name is the only account there is.
            case Quantity.NotRead<K> notRead -> whatTheSidesSay(left, right, notRead, ordered);
        };
    }

    /**
     * What a comparison whose arithmetic went unread comes to, off what its sides name.
     *
     * <p>Only here. Where the canonical form was read it has already said what the rule cuts, and a
     * spelling saying otherwise is the spelling being wrong about the rule.
     */
    private static <K> BlockReason.AboutARule whatTheSidesSay(ValueOrigin<K> left,
                                                              ValueOrigin<K> right,
                                                              Quantity.NotRead<K> notRead,
                                                              Predicate<K> ordered) {
        // What the sides name says nothing about whether anything fell short, and here something
        // did: the arithmetic stopped. A comparison naming two positions whose form was read is a
        // rule that relates them and leaves nothing missing, and one whose form was not read is a
        // rule nobody here has taken in — said alike, the second went out under a word that means
        // no measure is short of anything, and a model missing a border came back complete.
        // The carrier, asked of the position and before the reading. Whether a line can be drawn on
        // what a position holds is settled by the position, and no reader of any form would change
        // it — so `s < Won` over a type with one value says that, wherever the reading stopped.
        ValueOrigin<K> side = speakingSide(left, right);
        if (side instanceof ValueOrigin.IsAPosition<K> one && !ordered.test(one.at())) {
            return new BlockReason.UnreadComparisonDomain();
        }
        // And what the reading stopped at, where it stopped. Which expression that was is the
        // walk's answer and not something recovered from the sides: `String.length(s) > n * n`
        // stops at the product, and read off the sides it came back as a rule about the length —
        // an operation this reads, named for the one it does not.
        return whatThisSideSays(notRead.stoppedAt(), ordered);
    }

    /**
     * The side the reason is about.
     *
     * <p>The one that names a position, and the left where both do — which is the side a threshold
     * would be read off, and what is left over there is then what the coordinate was compared
     * against. Where neither names one, the side whose value came from a position: an author who
     * compared what a {@code map} answered wrote the rule about that side, and answering about the
     * literal beside it says the comparison was a form nobody could read when the form was never
     * the difficulty.
     */
    private static <K> ValueOrigin<K> speakingSide(ValueOrigin<K> left, ValueOrigin<K> right) {
        if (!left.positions().isEmpty()) {
            return left;
        }
        if (!right.positions().isEmpty()) {
            return right;
        }
        return left.madeFrom() != null ? left : right;
    }

    /** What one side leaves to say. */
    private static <K> BlockReason.AboutARule whatThisSideSays(ValueOrigin<K> side,
                                                               Predicate<K> ordered) {
        return switch (side) {
            // The position itself against something no end came out of. The carrier, asked of the
            // carrier: `at < DateTime(...)` stops because nothing draws a line on a date-time,
            // while `p.x < 1 + 2` stops because the other side is not a form a threshold is read
            // out of and `p.x` is an `Int` — a carrier lines are drawn on all through the file.
            case ValueOrigin.IsAPosition<K> one -> ordered.test(one.at())
                    ? new BlockReason.UnreadComparisonForm()
                    : new BlockReason.UnreadComparisonDomain();
            // A value an operation made of what stands at a position, and a rule written about that
            // value. Where it came from is known; what the rule says about the values there is not,
            // and working it out means following the rule back through the operation. One answer
            // for an operation over a position and for an element an operation handed out alike: a
            // rule about a sequence's elements is not a different kind of thing from a rule about a
            // number.
            case ValueOrigin.Applied<K> _, ValueOrigin.MadeFromAPosition<K> _ ->
                    new BlockReason.RuleAboutADerivedValue();
            // Arithmetic the terms do not take apart — unless what is under it came from a
            // position, which is the same rule about a value made from one with a layer of
            // arithmetic over it.
            case ValueOrigin.Composed<K> composed -> composed.madeFrom() != null
                    ? new BlockReason.RuleAboutADerivedValue()
                    : new BlockReason.UnreadComparisonForm();
            // A side that names nothing at all. Nothing is filed under this — a reason is said at
            // the positions the comparison names, and it names none — so what is answered is only
            // that no capability is owed on its account.
            case ValueOrigin.Written<K> _, ValueOrigin.Unnameable<K> _ ->
                    new BlockReason.UnreadComparisonForm();
        };
    }

    private UnreadComparison() {}
}
