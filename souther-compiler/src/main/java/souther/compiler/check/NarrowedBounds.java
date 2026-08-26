package souther.compiler.check;

import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;

/**
 * Where the rules of one value leave a coordinate, and which declarations are holding each end.
 *
 * <p>One answer and not two. Which declarations hold an end is a statement about that end and about
 * no other: it is worked out by taking a declaration's clauses away and seeing whether the end
 * moves, so it is only ever true of the number the reading it came from arrived at. Asked apart
 * from the end and put back together afterwards by the path and the side, the two came from
 * different readings of the same position — a case's own and the value a case was narrowed out of —
 * and the declaration holding one value's end was named as holding the other's ({@link #meet}).
 *
 * <p>Which is why no reading answers with the declarations alone. A caller that could ask for the
 * names without the number is a caller that will pair them with whatever end it has, and there is
 * no reading here to say whether that end is the one they are about. Taking them out of this to
 * carry across to a reading of another range is a decision, and it is made where that reading is.
 *
 * @param bounds where the coordinate stops either way, or null where nothing stops it at all
 * @param minBy  the declarations holding {@code bounds.min()}, empty where there is no such end
 * @param maxBy  the same at {@code bounds.max()}
 */
public record NarrowedBounds(NumericDomain.Bounds bounds,
                             List<TypeSymbol.AtModule> minBy,
                             List<TypeSymbol.AtModule> maxBy) {

    /** A coordinate the rules leave everything, which nobody is holding either way. */
    public static final NarrowedBounds NOTHING = new NarrowedBounds(null, List.of(), List.of());

    public NarrowedBounds {
        minBy = canonical(minBy);
        maxBy = canonical(maxBy);
        // An absent end is not one a declaration moved. The rules leaving a coordinate everything on
        // one side is not a state any clause brought about, and a name held against it would be a
        // reader's licence to report an infinity as narrowed by somebody.
        if (endOf(bounds, true) == null && !minBy.isEmpty()) {
            throw new IllegalArgumentException(
                    "no lower end to hold, and " + minBy + " named as holding it");
        }
        if (endOf(bounds, false) == null && !maxBy.isEmpty()) {
            throw new IllegalArgumentException(
                    "no upper end to hold, and " + maxBy + " named as holding it");
        }
    }

    /**
     * What two readings of one coordinate leave it, and who is holding what they leave.
     *
     * <p>The ends meet, and the declarations follow the end that survived. A reading whose end lies
     * further out than the other's is holding an end this coordinate does not stop at, so what it
     * names is out — naming it would send an author to a clause that moved this end nowhere, which
     * is the one thing the reading below refuses to do when it is asked over one set of rules.
     *
     * <p>Both where both readings arrive at the same end. Neither of them settled it alone and each
     * is as much the answer as the other, which is what the reading below answers when two clauses
     * of one value say what one edge says.
     *
     * <p>The end and not the place it stands at, and the end and not how it was written. Both are
     * {@link Endpoint#sameAs}'s business: {@code (3, inclusive)} and {@code (3, exclusive)} are two
     * ends and a conjunction leaves the second, while {@code 3.0} and {@code 3.00} are one end
     * written twice. Asked with a derived equality, the first pair comes back as one — and the
     * second as two, so which reading is holding the end would turn on which of them spelled the
     * number the way the meet happened to keep.
     */
    public NarrowedBounds meet(NarrowedBounds other) {
        if (other == null) {
            return this;
        }
        NumericDomain.Bounds met = bounds == null ? other.bounds
                : other.bounds == null ? bounds : bounds.meet(other.bounds);
        return new NarrowedBounds(met, holding(met, other, true), holding(met, other, false));
    }

    /** Which of the two readings' names survive at the end {@code met} leaves on this side. */
    private List<TypeSymbol.AtModule> holding(NumericDomain.Bounds met, NarrowedBounds other,
                                              boolean lower) {
        Endpoint end = endOf(met, lower);
        if (end == null) {
            // Asked before either reading is compared, so that two readings with no end on this side
            // are not read as agreeing about one. There is no end here for anybody to be holding.
            return List.of();
        }
        List<TypeSymbol.AtModule> out = new ArrayList<>();
        if (end.sameAs(endOf(bounds, lower))) {
            out.addAll(lower ? minBy : maxBy);
        }
        if (end.sameAs(endOf(other.bounds, lower))) {
            out.addAll(lower ? other.minBy : other.maxBy);
        }
        return out;
    }

    /** Where these ends stop on one side, or null where nothing does. */
    private static Endpoint endOf(NumericDomain.Bounds bounds, boolean lower) {
        return bounds == null ? null : lower ? bounds.min() : bounds.max();
    }

    /**
     * The declarations in one order and each of them once.
     *
     * <p>Several of these are one answer, and an order read off the walk that collected them would
     * make two readings of one edge into two answers. The same order {@link FieldDomains} settles a
     * single reading's names in, because these are the same names met.
     */
    private static List<TypeSymbol.AtModule> canonical(List<TypeSymbol.AtModule> found) {
        return found.stream().distinct().sorted().toList();
    }
}
