package souther.compiler.partition;

/**
 * What a row away from a border's line is owed for, beside the line itself.
 *
 * <p>The two points against a line are values of the quantity, and the line settles them wherever it
 * is read. The other two are the regions either side, and a region is settled by the line and by
 * whatever stops it on the far side — so what tells two of them apart is that far side, and this is
 * it.
 *
 * <p><b>Two shapes, because a rule leaves two kinds of region.</b> A rule that orders the values
 * around its line leaves a run beside it, and the run stops somewhere ({@link Beside}). A rule that
 * names one value instead leaves everything else, which is not a run and stops nowhere
 * ({@link TheRest}) — a bound's far side is refused outright and an equality's is the whole of the
 * quantity but one value.
 *
 * <p>Made where the region is, and never read back off what it came to. Which of the two a border
 * owes is decided by the rule that drew it, and a reader that saw a criterion over everything-but-one
 * and called it the second would be answering from the shape of the demand rather than from the rule.
 */
public sealed interface RegionBasis {

    /**
     * A run beside the line, stopping at {@code farEnd}.
     *
     * <p>One of these per thing that could have stopped it, since each is enough on its own: a place
     * two rules drew a line at leaves two, and a row inside the run answers both.
     */
    record Beside(FarEnd farEnd) implements RegionBasis {

        public Beside {
            if (farEnd == null) {
                throw new IllegalArgumentException("a run beside the line stops somewhere");
            }
        }
    }

    /**
     * Everything the quantity takes but the line's own value.
     *
     * <p>What a rule that names a value leaves. Nothing is carried: which value is left out is the
     * line's, and the line is what a debt is already keyed on.
     */
    enum TheRest implements RegionBasis {
        INSTANCE
    }
}
