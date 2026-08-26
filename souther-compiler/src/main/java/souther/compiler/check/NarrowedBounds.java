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
 * <p>Which is why there is no way to ask for the declarations alone. A caller with the names and
 * without the number is a caller that will pair them with whatever end it has.
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

    /** These ends and nobody holding them, which is what a reading that relates nothing arrives at. */
    public static NarrowedBounds held(NumericDomain.Bounds bounds) {
        return bounds == null ? NOTHING : new NarrowedBounds(bounds, List.of(), List.of());
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
     * <p>The end and not the place it stands at. {@code (3, inclusive)} and {@code (3, exclusive)}
     * are two ends and the second is the one a conjunction leaves; read as one because the number is
     * the same, the value that stops at 3 would be reported as held by a clause that admits it.
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
        if (end.equals(endOf(bounds, lower))) {
            out.addAll(lower ? minBy : maxBy);
        }
        if (end.equals(endOf(other.bounds, lower))) {
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
