package souther.compiler.check;

import souther.compiler.inputs.BlockReason;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
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
 * <p><b>Two questions, and which of them is asked turns on whether there is a quantity.</b> Where
 * the arithmetic reached one, the quantity is what the rule is about: it says what the rule leaves
 * and, through {@link #filedAt}, which of the places the walk met are the rule's at all. Where the
 * arithmetic stopped there is no quantity to be about, so each place is asked for itself and the
 * reader says what filing there means ({@link RuleAt}).
 *
 * <p>So no answer here is read off a side of the comparison. One was: the reason was worked out
 * once from whichever side named a position, and every place the comparison mentioned was handed
 * the result — after which a rule about {@code n} told {@code l1.l2.leaf} what {@code n}'s carrier
 * carries, and a position the canonical form had cancelled was told a form nobody could read
 * stopped at it.
 *
 * <p>What a position is called travels with the answers and is never read here, only compared with
 * another of its own. So the readers may hold a position under whatever name each of them uses and
 * still be held to one rule.
 */
public final class UnreadComparison {

    /**
     * What the arithmetic made of the comparison.
     *
     * <p>Two cases at the top and not four, because the two questions below divide here. A reading
     * that reached a quantity has a subject; one that stopped has none, and the difference decides
     * which of them a caller may ask. Flat, a caller with a stopped reading could ask for the
     * quantity's answer and be given one about a subject that was never established.
     *
     * <p><b>Each of them carries what it stands for.</b> A quantity over nothing is not a quantity,
     * and a reading that stopped is not one without somewhere it stopped — held as cases that can be
     * made from nothing, one of them stands in for another and whoever reads it reconstructs the
     * difference from whatever else is to hand.
     */
    public sealed interface Quantity<K> {

        /**
         * The arithmetic read the comparison to the end, and this is the quantity it cuts.
         *
         * <p>Which positions that quantity runs over is what the rule is about. A position the
         * canonical form cancelled is named by the comparison and is no subject of it: {@code a + b
         * - b + c <= 10} is {@code a + c <= 10}, and a note at {@code b} would say the rule relates
         * a position it does not mention.
         */
        sealed interface Read<K> extends Quantity<K> {

            /** The positions the quantity runs over, which may be none. */
            Set<K> support();
        }

        /**
         * The quantity this comparison cuts is over several positions, so it divides none of them.
         *
         * <p>Several and not one, by the type. A form over one position is a line on that
         * position as far as the arithmetic goes, and what a caller could make of it is a
         * different question with a different answer ({@link OverOne}) — counted as one of these
         * by the size of a set, the two were told apart by whoever held the set.
         */
        record OverSeveral<K>(Set<K> positions) implements Read<K> {

            public OverSeveral {
                positions = java.util.Collections.unmodifiableSet(new LinkedHashSet<>(positions));
                if (positions.size() < 2) {
                    // A quantity over no position is what {@link CutsNothing} says and one over a
                    // single position is {@link OverOne}; saying either here lets a reader answer
                    // one of them for the other.
                    throw new IllegalArgumentException(
                            "a quantity over several positions is over at least two");
                }
            }

            @Override
            public Set<K> support() {
                return positions;
            }
        }

        /**
         * The quantity this comparison cuts is over one position: the arithmetic read a line on it.
         *
         * <p>A caller holding one of these and still asking what would have to change is one whose
         * own reading of the line placed none — a reader of ends that takes a coordinate against
         * a written constant, handed {@code x + 1 <= 10}. That reading stopped, on a form the
         * arithmetic reads, and what it stopped on is the position and its carrier: nothing about
         * how the sides were spelled adds to that, and asked of the sides this answered about a
         * shape the arithmetic had already got past.
         */
        record OverOne<K>(K position) implements Read<K> {

            public OverOne {
                if (position == null) {
                    throw new IllegalArgumentException("a quantity over one position names it");
                }
            }

            @Override
            public Set<K> support() {
                return Set.of(position);
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
         *
         * <p>The one quantity whose places are not its support. There is nothing in the support to
         * file at, and what makes the rule worth saying at all is that the model names a position
         * there and cuts nothing — so this alone is filed where the comparison names.
         */
        record CutsNothing<K>() implements Read<K> {

            @Override
            public Set<K> support() {
                return Set.of();
            }
        }

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
     * Which of the places a walk met a read comparison is filed at, in the order it met them.
     *
     * <p>The quantity decides, and the walk only says what each place is called and which came
     * first. Membership taken from the walk instead, a rule was filed at positions its own
     * canonical form had cancelled — and the word it left there was the word for the position the
     * quantity does cut.
     *
     * <p>{@link Quantity.CutsNothing} is the exception, and a deliberate one: its support is empty
     * and there would be nothing to file, while what the rule is worth saying for is that the model
     * states something at the positions it names and cuts none of them.
     */
    public static <K> List<K> filedAt(Quantity.Read<K> read, List<K> met) {
        if (read instanceof Quantity.CutsNothing<K>) {
            return List.copyOf(met);
        }
        List<K> out = new ArrayList<>();
        for (K each : met) {
            if (read.support().contains(each)) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * What a comparison the arithmetic read to the end leaves, at the places it is filed at.
     *
     * <p>One answer for all of them, because the quantity is one subject. Which places those are is
     * {@link #filedAt}'s, and every one of them is a position this quantity runs over — or, for a
     * quantity that runs over none, a position the rule names and cuts nothing of.
     *
     * @param ordered whether a line can be drawn on what a position carries, asked of the carrier.
     *                Asked of the reader because a position is looked up there, and asked at all
     *                only about the one position a quantity over one is on
     */
    public static <K> BlockReason.RuleWithoutLineReason ofTheQuantity(Quantity.Read<K> read,
                                                                     Predicate<K> ordered) {
        return switch (read) {
            // Read to the end and there is no quantity. Nothing about how it was written adds to
            // that: no reading fell short, so no question about what could not be read arises.
            case Quantity.CutsNothing<K> _ -> new BlockReason.ComparisonCuttingNothing();
            case Quantity.OverSeveral<K> _ -> new BlockReason.ComparisonBetweenPositions();
            // A line on one position that the caller's own reading placed nowhere: that reading
            // stopped, and what it stopped on is the position. The carrier says which limit — a
            // position nothing draws a line on wants the carrier, and one lines are drawn on all
            // through the file wants a reader of the form.
            case Quantity.OverOne<K> one -> ordered.test(one.position())
                    ? new BlockReason.UnreadComparisonForm()
                    : new BlockReason.UnreadComparisonDomain();
        };
    }

    /**
     * What a reading that stopped leaves at one place it was filed at.
     *
     * <p>Typed as a stop, because that is what every answer here is: the arithmetic stopped, and
     * what is left to decide is which limit it stopped on. A caller that has met a stop and wants
     * the words for it asks this, and cannot be handed the words for a rule read to the end —
     * those are answers about a quantity, and this is never given one.
     *
     * <p><b>What the reading stopped at first, and the carrier only after.</b> Where the value the
     * rule speaks of was made by an operation, following the rule back through that operation is
     * the capability that is missing, and it is missing whatever the position carries. Asked the
     * other way round, a rule about what a call answered of a field with no order of its own was
     * reported as a rule this could draw no line on — sending its author to values the rule never
     * mentions.
     *
     * <p>And the carrier is asked only where the rule is about the values at the place it is filed
     * at, which the reader says. Asked at every place, a rule about {@code n} answered about what
     * {@code l1.l2.leaf} carries, because that is where the walk met a position on its way through
     * an expression it could not take apart.
     */
    public static <K> BlockReason.RuleReadingStopped whereItStopped(RuleAt<K> at,
                                                                   Quantity.NotRead<K> notRead,
                                                                   Predicate<K> ordered) {
        // A value an operation made of what stands at a position, and a rule written about that
        // value. Where it came from is known; what the rule says about the values there is not,
        // and working it out means following the rule back through the operation. One answer for
        // an operation over a position and for an element an operation handed out alike: a rule
        // about a sequence's elements is not a different kind of thing from a rule about a number.
        if (madeByAnOperation(notRead.stoppedAt())) {
            return new BlockReason.RuleAboutADerivedValue();
        }
        return switch (at) {
            // The values here are what the rule speaks of, so what they are carried on says which
            // limit stopped the reading: `at < DateTime(...)` stops because nothing draws a line on
            // a date-time, while `p.x < 1 + 2` stops because the other side is not a form a
            // threshold is read out of and `p.x` is an `Int` — a carrier lines are drawn on all
            // through the file.
            case RuleAt.AboutOwnValues<K> own -> ordered.test(own.position())
                    ? new BlockReason.UnreadComparisonForm()
                    : new BlockReason.UnreadComparisonDomain();
            // And where they are not, there is no question about this carrier to answer. What is
            // left is the form: something is written here that this did not read, and which of the
            // position's numbers it was about is the part that went unread.
            case RuleAt.NotAboutOwnValues<K> _ -> new BlockReason.UnreadComparisonForm();
        };
    }

    /** Whether what a reading stopped at is a value an operation made of a position. */
    private static <K> boolean madeByAnOperation(ValueOrigin<K> stoppedAt) {
        return switch (stoppedAt) {
            case ValueOrigin.Applied<K> _, ValueOrigin.MadeFromAPosition<K> _ -> true;
            // Arithmetic the terms do not take apart — unless what is under it came from a
            // position, which is the same rule about a value made from one with a layer of
            // arithmetic over it.
            case ValueOrigin.Composed<K> composed -> composed.madeFrom() != null;
            case ValueOrigin.IsAPosition<K> _, ValueOrigin.Written<K> _,
                 ValueOrigin.Unnameable<K> _ -> false;
        };
    }

    private UnreadComparison() {}
}
