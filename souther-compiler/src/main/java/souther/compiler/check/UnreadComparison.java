package souther.compiler.check;

import souther.compiler.inputs.BlockReason;

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
 */
public final class UnreadComparison {

    /**
     * What one side of a comparison came to, as the reader that looked it up found it.
     *
     * <p>Three cases and not a pair of flags. Whether the position this side names carries an order
     * is a question only about a side that is a position, and a reader handing over an answer for a
     * side that names none would be filling in a field that stands for nothing.
     */
    public sealed interface Side {

        /** Nothing here is one of the positions being read for. */
        record NamesNothing() implements Side {}

        /**
         * A position is named from inside an expression this reader does not take apart:
         * {@code Int.add(length, width)}, {@code p.x + 1}.
         *
         * <p>What is missing is a reading of the form. Nothing is known about the order under the
         * position from here — the expression is what was not read — so nothing about it is said.
         */
        record HoldsOne() implements Side {}

        /**
         * This side is the position itself, or a number taken of it.
         *
         * @param ordered whether a line can be drawn on what that position carries, asked of the
         *                carrier
         */
        record IsOne(boolean ordered) implements Side {}
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
     */
    public static BlockReason why(Side left, Side right) {
        if (!(left instanceof Side.NamesNothing) && !(right instanceof Side.NamesNothing)) {
            return new BlockReason.ComparisonBetweenPositions();
        }
        return switch (left instanceof Side.NamesNothing ? right : left) {
            // The position itself against something no end came out of. The carrier, asked of the
            // carrier: `at < DateTime(...)` stops because nothing draws a line on a date-time,
            // while `p.x < 1 + 2` stops because the other side is not a form a threshold is read
            // out of and `p.x` is an `Int` — a carrier lines are drawn on all through the file.
            case Side.IsOne one -> one.ordered() ? new BlockReason.UnreadComparisonForm()
                    : new BlockReason.UnreadComparisonDomain();
            case Side.HoldsOne _ -> new BlockReason.UnreadComparisonForm();
            // Neither side names a position. Nothing is filed under this — a reason is said at the
            // positions the comparison names, and it names none — so what is answered is only that
            // no capability is owed on its account.
            case Side.NamesNothing _ -> new BlockReason.UnreadComparisonForm();
        };
    }

    private UnreadComparison() {}
}
