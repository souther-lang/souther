package souther.compiler.check;

import souther.compiler.inputs.BlockReason;

import java.util.LinkedHashSet;
import java.util.Set;

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
 * <p>What a position is called travels with the answers and is never read here, only compared with
 * another of its own. So the readers may hold a position under whatever name each of them uses and
 * still be held to one rule.
 */
public final class UnreadComparison {

    /**
     * What one side of a comparison came to, as the reader that looked it up found it.
     *
     * <p>Three cases and not a pair of flags. Whether the position this side names carries an order
     * is a question only about a side that is a position, and a reader handing over an answer for a
     * side that names none would be filling in a field that stands for nothing.
     *
     * <p>Each carries which positions it named and not only that it named some. Which two positions
     * a comparison is between is the question the rule below asks, and a side that answered only
     * "one of them is in here" made {@code x < x + 1} a rule about {@code x} and something else.
     */
    public sealed interface Side<K> {

        /** The positions this side names, in the order the reader met them. */
        Set<K> positions();

        /** Nothing here is one of the positions being read for. */
        record NamesNothing<K>() implements Side<K> {

            @Override
            public Set<K> positions() {
                return Set.of();
            }
        }

        /**
         * Positions are named from inside an expression this reader does not take apart:
         * {@code Int.add(length, width)}, {@code p.x + 1}.
         *
         * <p>However many of them. What is missing is a reading of the form, and nothing is known
         * about the order under any position from here — the expression is what was not read — so
         * nothing about that is said.
         */
        record NamesInside<K>(Set<K> positions) implements Side<K> {

            public NamesInside {
                positions = java.util.Collections.unmodifiableSet(new LinkedHashSet<>(positions));
            }
        }

        /**
         * This side is the position itself, or a number taken of it.
         *
         * @param ordered whether a line can be drawn on what that position carries, asked of the
         *                carrier
         */
        record IsOne<K>(K position, boolean ordered) implements Side<K> {

            @Override
            public Set<K> positions() {
                return Set.of(position);
            }
        }
    }

    /**
     * What would have to change before this comparison could be a line.
     *
     * <p>Three different things, and a reader told one sentence for all of them cannot tell which
     * limit is theirs to wait on. A comparison between two positions asks for a class that is about
     * both, which a partition of one position is not. One on a carrier nothing draws a line on asks
     * for that carrier. What is left is a form this does not read — the position inside an
     * expression the terms do not name, or a threshold written as something other than a constant.
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
     * the same division of labour {@link Side} already has. Where the arithmetic reads nothing there
     * is no quantity to count, and the sides answer: {@code a > b} over strings relates two
     * positions on an order with no numbers, and {@code a * b > 5} names two and is stopped by
     * neither of them.
     *
     * @param quantityIsOver the positions the canonical form's quantity is over, or null where the
     *                       arithmetic read no form at all
     */
    public static <K> BlockReason why(Side<K> left, Side<K> right,
                                      Set<K> quantityIsOver) {
        // What the rule cuts, where the arithmetic could be read at all. A quantity over
        // more than one position divides none of them — which values of one are on which
        // side depends on the others — and that is as true of `3a + 6b <= 48`, whose two
        // sit on one side, as of `a < b`. Counted off the sides instead, the first came
        // back as a form nobody could read; counted off how many positions the comparison
        // names, `a * b > 5` came back as a relation when what stops it is the product.
        if (quantityIsOver != null && quantityIsOver.size() > 1) {
            return new BlockReason.ComparisonBetweenPositions();
        }
        return whatTheSidesSay(left, right);
    }

    /** The same, where the arithmetic named no quantity — which is every carrier whose
     *  values do not count, and every form outside the affine fragment. */
    private static <K> BlockReason whatTheSidesSay(Side<K> left, Side<K> right) {
        Set<K> named = new LinkedHashSet<>(left.positions());
        named.addAll(right.positions());
        if (!left.positions().isEmpty() && !right.positions().isEmpty() && named.size() > 1) {
            return new BlockReason.ComparisonBetweenPositions();
        }
        // The side that names one, and the left where both do — which is the side a threshold would
        // be read off. What is left over there is then what the coordinate was compared against.
        return switch (left.positions().isEmpty() ? right : left) {
            // The position itself against something no end came out of. The carrier, asked of the
            // carrier: `at < DateTime(...)` stops because nothing draws a line on a date-time,
            // while `p.x < 1 + 2` stops because the other side is not a form a threshold is read
            // out of and `p.x` is an `Int` — a carrier lines are drawn on all through the file.
            case Side.IsOne<K> one -> one.ordered() ? new BlockReason.UnreadComparisonForm()
                    : new BlockReason.UnreadComparisonDomain();
            case Side.NamesInside<K> _ -> new BlockReason.UnreadComparisonForm();
            // Neither side names a position. Nothing is filed under this — a reason is said at the
            // positions the comparison names, and it names none — so what is answered is only that
            // no capability is owed on its account.
            case Side.NamesNothing<K> _ -> new BlockReason.UnreadComparisonForm();
        };
    }

    private UnreadComparison() {}
}
