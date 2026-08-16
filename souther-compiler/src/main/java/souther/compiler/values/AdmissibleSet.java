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
 * What a reader may do with it follows from that alone, and the three are deliberately not the
 * same list:
 *
 * <pre>
 *     narrow with it            in every row — a class holding none of its values holds none
 *     make classes out of it    wherever it is finite — the values are the ones the model named
 *     call it exact             only under Complete
 * </pre>
 *
 * <p>The middle one is the row to keep. A finite set read beside a rule this could not take in
 * names the same values the model singled out, and the classes are the same classes; what the
 * completeness beside it settles is what may be said about them afterwards — that a rule which went
 * unread may yet refuse one — and not whether there are any. A reading that made classes only under
 * {@code Complete} would leave the two spellings of one distinction measured differently again, the
 * sum keeping its cases beside a rule nothing could read and the enumeration losing them.
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

    /** Every rule about the position was read, which is what a reader holding no reading of its own
     * starts from. */
    public static final Completeness READ_IN_FULL = new Completeness.Complete();

    /** The whole of what the rules leave the position. */
    public static AdmissibleSet complete(ValueSet values) {
        return new AdmissibleSet(values, READ_IN_FULL);
    }

    /** These values, with something about the position left unread. */
    public static AdmissibleSet partial(ValueSet values, UnreadReason why) {
        return new AdmissibleSet(values, new Completeness.Partial(why));
    }

    /** Why the reading is short of the rules, or null where it is not short of them. */
    public UnreadReason whyPartial() {
        return completeness instanceof Completeness.Partial partial ? partial.why() : null;
    }
}
