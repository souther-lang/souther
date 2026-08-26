package souther.compiler.check;

import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.function.Supplier;

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
 * <p>Which is why no reading answers with the declarations alone, and why one of these is only ever
 * made by a reading. A caller that could ask for the names without the number, or write down a
 * pairing of its own, is a caller that will put them beside whatever end it has — and there is no
 * reading there to say whether that end is the one they are about. Taking them out of this to carry
 * across to a reading of another range is a decision, and it is made where that reading is.
 *
 * <p><b>The names are worked out when they are asked for.</b> Reading a declaration again without
 * one declaration's clauses is what answers who holds an end, and it is done once per candidate and
 * per side — while where the coordinate stops is a lookup. The two are not the same price, and a
 * caller standing a fixture in a coordinate's range wants only the cheap half. Nor is this a saving
 * made against the meaning: an end that loses a meet has nobody worth naming, and working the names
 * out before the ends are met is doing the arithmetic in the order that throws the answer away.
 *
 * <p>Comparing, hashing or printing one of these asks for the names, which is the one way to reach
 * that work without meaning to. It is worth knowing where one of these is used as a map key.
 */
public final class NarrowedBounds {

    /** A coordinate the rules leave everything, which nobody is holding either way. */
    public static final NarrowedBounds NOTHING = new NarrowedBounds(null, Held.NONE, Held.NONE);

    private final NumericDomain.Bounds bounds;
    private final Held minBy;
    private final Held maxBy;

    private NarrowedBounds(NumericDomain.Bounds bounds, Held minBy, Held maxBy) {
        this.bounds = bounds;
        this.minBy = minBy;
        this.maxBy = maxBy;
    }

    /**
     * These ends, held by these declarations.
     *
     * <p>Not offered outside this reading, and this is the whole of what keeps the two together. A
     * caller that could write one of these down could pair one reading's ends with another
     * reading's names, which is the answer this exists to stop being possible — and there would be
     * nothing left saying so except the sentence above.
     */
    NarrowedBounds(NumericDomain.Bounds bounds, List<TypeSymbol.AtModule> minBy,
                   List<TypeSymbol.AtModule> maxBy) {
        this(bounds, held(bounds, true, minBy), held(bounds, false, maxBy));
    }

    /**
     * The same, with the names left to be worked out.
     *
     * <p>Not offered outside this reading. A caller that could hand over work to be done later is a
     * caller deciding when a declaration is read, which is this package's answer to give.
     *
     * <p>A side with no end holds nobody whatever the work would have said, so that side is settled
     * here and the work is never asked for. Which is what keeps "an absent end is nobody's" a
     * statement about this value rather than a hope about what a supplier will return.
     */
    static NarrowedBounds deferred(NumericDomain.Bounds bounds,
                                   Supplier<List<TypeSymbol.AtModule>> minBy,
                                   Supplier<List<TypeSymbol.AtModule>> maxBy) {
        return new NarrowedBounds(bounds,
                endOf(bounds, true) == null ? Held.NONE : new Held(minBy),
                endOf(bounds, false) == null ? Held.NONE : new Held(maxBy));
    }

    /** Where the coordinate stops either way, or null where nothing stops it at all. */
    public NumericDomain.Bounds bounds() {
        return bounds;
    }

    /** The declarations holding {@code bounds().min()}, empty where there is no such end. */
    public List<TypeSymbol.AtModule> minBy() {
        return minBy.names();
    }

    /** The same at {@code bounds().max()}. */
    public List<TypeSymbol.AtModule> maxBy() {
        return maxBy.names();
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
     *
     * <p>Which end survives is settled here; who is holding it is not. The reading that lost is
     * never asked on that side, and knowing which one lost is what the ends had to be met for.
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
    private Held holding(NumericDomain.Bounds met, NarrowedBounds other, boolean lower) {
        Endpoint end = endOf(met, lower);
        if (end == null) {
            // Settled before either reading is compared, so that two readings with no end on this
            // side are not read as agreeing about one. There is no end here for anybody to hold.
            return Held.NONE;
        }
        boolean mine = end.sameAs(endOf(bounds, lower));
        boolean theirs = end.sameAs(endOf(other.bounds, lower));
        if (!mine) {
            return theirs ? other.side(lower) : Held.NONE;
        }
        if (!theirs) {
            return side(lower);
        }
        return new Held(() -> {
            List<TypeSymbol.AtModule> out = new ArrayList<>(side(lower).names());
            out.addAll(other.side(lower).names());
            return out;
        });
    }

    private Held side(boolean lower) {
        return lower ? minBy : maxBy;
    }

    /** Where these ends stop on one side, or null where nothing does. */
    private static Endpoint endOf(NumericDomain.Bounds bounds, boolean lower) {
        return bounds == null ? null : lower ? bounds.min() : bounds.max();
    }

    /** Names written against an end, refused where there is no end to hold. */
    private static Held held(NumericDomain.Bounds bounds, boolean lower,
                             List<TypeSymbol.AtModule> names) {
        if (endOf(bounds, lower) != null) {
            return new Held(names);
        }
        // An absent end is not one a declaration moved. The rules leaving a coordinate everything on
        // one side is not a state any clause brought about, and a name held against it would be a
        // reader's licence to report an infinity as narrowed by somebody.
        if (!names.isEmpty()) {
            throw new IllegalArgumentException("no " + (lower ? "lower" : "upper")
                    + " end to hold, and " + names + " named as holding it");
        }
        return Held.NONE;
    }

    /**
     * Two of these are one where they hold the same ends as written and the same declarations.
     *
     * <p>The ends as written, and not the ends. {@link Endpoint#sameAs} is what says two ends stop a
     * coordinate in one spot, and this is not it: {@code 3} and {@code 3.00} come back different
     * here, because what the ends hold is what a report writes back and a caller comparing two of
     * these is comparing what was read. Which of the two questions a reader wants is the reader's,
     * and the one about where the coordinate stops is asked of the ends themselves.
     *
     * <p>This asks for the names, so comparing, hashing or printing one of these does the work the
     * names were left to do later — the one exception to their being worked out only when they are
     * asked for. A caller that compares what a coordinate came to has decided to read all of it.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof NarrowedBounds it && Objects.equals(bounds, it.bounds)
                && minBy().equals(it.minBy()) && maxBy().equals(it.maxBy());
    }

    @Override
    public int hashCode() {
        return Objects.hash(bounds, minBy(), maxBy());
    }

    @Override
    public String toString() {
        return "NarrowedBounds[bounds=" + bounds + ", minBy=" + minBy() + ", maxBy=" + maxBy() + "]";
    }

    /**
     * The declarations holding one end, worked out at most once.
     *
     * <p>Kept rather than worked out where the value is made, because working them out reads the
     * declaration again once per candidate and most readers of a coordinate's range never ask. What
     * is kept afterwards is the answer and not the work, so one of these answers the same thing
     * however often it is asked and whoever asks first pays.
     */
    private static final class Held {

        /** An end nobody is holding, which is what a side with no end has and what a reading that
         *  relates nothing arrives at. */
        static final Held NONE = new Held(List.of());

        private Supplier<List<TypeSymbol.AtModule>> work;
        private List<TypeSymbol.AtModule> found;

        Held(List<TypeSymbol.AtModule> found) {
            this.found = canonical(found);
        }

        Held(Supplier<List<TypeSymbol.AtModule>> work) {
            this.work = work;
        }

        synchronized List<TypeSymbol.AtModule> names() {
            if (found == null) {
                found = canonical(work.get());
                work = null;
            }
            return found;
        }

        /**
         * The declarations in one order and each of them once.
         *
         * <p>Several of these are one answer, and an order read off the walk that collected them
         * would make two readings of one edge into two answers. The same order {@link FieldDomains}
         * settles a single reading's names in, because these are the same names met.
         */
        private static List<TypeSymbol.AtModule> canonical(List<TypeSymbol.AtModule> found) {
            return found.stream().distinct().sorted().toList();
        }
    }
}
