package souther.compiler.values;

/**
 * Which values a position may hold, and how much of what the rules say about it was read.
 *
 * <p>Two axes and not two answers. What was found and how far the finding got are orthogonal — a
 * set of two values read in full and the same set read beside a rule this could not take in are the
 * same set — and a caller needs both to do anything with either. Written as a product so that
 * neither can be taken without the other, and so that what each combination licenses can be stated
 * once as a table rather than rediscovered at each reader:
 *
 * <pre>
 *     Finite(S),   Complete    the model divides the position into exactly these values
 *     Finite(S),   Partial     these values, and the rules may leave fewer
 *     Cofinite(E), Complete    the model excludes these and divides nothing
 *     Cofinite(E), Partial     the same, and the rules may exclude more
 *     ANY,         Complete    the model says nothing about which values stand here
 *     ANY,         Partial     this reading says nothing, which is not the model saying nothing
 * </pre>
 *
 * <p>The last row is the one the product exists for. It reads exactly like the row above it and
 * means the opposite to anyone deciding whether a position is one the model draws no distinction
 * at.
 *
 * <p>{@link #approximation} is an upper bound in every row: everything it excludes is excluded.
 * That is what lets a reader narrow with it whatever the completeness beside it says, and it is
 * only under {@link Completeness.Complete} that the set is the whole of what the rules leave.
 */
public record AdmissibleSet(ValueSet approximation, Completeness completeness) {

    public AdmissibleSet {
        if (approximation == null || completeness == null) {
            throw new IllegalArgumentException("a set with no values or no account of itself");
        }
    }

    /** How much of what the rules say was read. */
    public sealed interface Completeness {

        /** Every rule reaching the position was taken into the set. */
        record Complete() implements Completeness {}

        /**
         * Something about the position went unread, so the set is wider than the rules are.
         *
         * <p>Which of the kinds it was is carried because they are lifted by different work and
         * reported differently; what a reader does with the set is the same for all of them.
         */
        record Partial(UnreadReason why) implements Completeness {

            public Partial {
                if (why == null) {
                    throw new IllegalArgumentException("a partial reading knows why it is partial");
                }
            }
        }
    }

    private static final Completeness COMPLETE = new Completeness.Complete();

    /** The whole of what the rules leave the position. */
    public static AdmissibleSet complete(ValueSet values) {
        return new AdmissibleSet(values, COMPLETE);
    }

    /** These values, with something about the position left unread. */
    public static AdmissibleSet partial(ValueSet values, UnreadReason why) {
        return new AdmissibleSet(values, new Completeness.Partial(why));
    }

    /** Whether the set is the whole of what the rules leave, rather than an upper bound on it. */
    public boolean isComplete() {
        return completeness instanceof Completeness.Complete;
    }

    /** Why the reading is short of the rules, or null where it is not short of them. */
    public UnreadReason whyPartial() {
        return completeness instanceof Completeness.Partial partial ? partial.why() : null;
    }
}
