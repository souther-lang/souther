package souther.compiler.check;

import souther.compiler.numeric.EndSide;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Objects;
import java.util.Optional;
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
 * <p><b>The names are never handed over on their own.</b> There is no way to ask this what it holds
 * without saying which end you are asking about: {@link #matching} takes the end the caller has, and
 * answers with the names only where that is the end they were worked out against. A caller that
 * could ask for the names alone is a caller that will put them beside whatever end it has, and there
 * is no reading there to say whether that end is the one they are about.
 *
 * <p><b>Three readings cross an end, and they all cross it the same way.</b> Two of them are
 * elsewhere — a position's cuts are drawn against the range every rule reaching it leaves, and a
 * border's runs against what the whole behavior leaves the term — and {@link #meet} is the third,
 * here because both of its readings are. All three ask {@link #matching}; they differ only in what
 * they do with what comes back. Left to work the comparison out for themselves, one invariant would
 * have three implementations to keep in step.
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
public abstract sealed class NarrowedBounds {

    /** A coordinate the rules leave everything, which nobody is holding either way. */
    public static final NarrowedBounds NOTHING = new Nothing();

    private NarrowedBounds() {}

    /**
     * These ends, held by these declarations.
     *
     * <p>Not offered outside this reading, and this is the whole of what keeps the two together. A
     * caller that could write one of these down could pair one reading's ends with another
     * reading's names, which is the answer this exists to stop being possible — and there would be
     * nothing left saying so except the sentence above.
     */
    static NarrowedBounds of(NumericDomain.Bounds bounds, List<TypeSymbol.AtModule> minBy,
                             List<TypeSymbol.AtModule> maxBy) {
        return read(bounds, end(bounds, EndSide.LOWER, minBy), end(bounds, EndSide.UPPER, maxBy));
    }

    /**
     * The same, with the names left to be worked out.
     *
     * <p>Not offered outside this reading. A caller that could hand over work to be done later is a
     * caller deciding when a declaration is read, which is this package's answer to give.
     *
     * <p>A side with no end holds nobody whatever the work would have said, so that side has no end
     * here at all and the work is never asked for. Which is what keeps "an absent end is nobody's" a
     * statement about which values this has rather than a hope about what a supplier will return.
     */
    static NarrowedBounds deferred(NumericDomain.Bounds bounds,
                                   Supplier<List<TypeSymbol.AtModule>> minBy,
                                   Supplier<List<TypeSymbol.AtModule>> maxBy) {
        return read(bounds, deferredEnd(bounds, EndSide.LOWER, minBy),
                deferredEnd(bounds, EndSide.UPPER, maxBy));
    }

    /** Where the coordinate stops either way, or null where nothing stops it at all. */
    public abstract NumericDomain.Bounds bounds();

    /**
     * The declarations holding {@code target}, where that is the end this reading leaves on
     * {@code side}, and nothing where it is not.
     *
     * <p>The one way names leave a reading. {@link Endpoint#sameAs} is what says two ends stop a
     * coordinate in one spot — {@code 3} and {@code 3.00} are one end written twice, while
     * {@code (3, inclusive)} and {@code (3, exclusive)} are two ends — and the side is asked beside
     * it because a range holding one value stops at that value both ways.
     *
     * <p>An answer here is not a licence to print the names. It says they are about this end; what
     * a report owes at it is the asking consumer's own question.
     *
     * <p>A {@code null} target is a caller whose own reading stops the coordinate nowhere on that
     * side, and nothing is what this reading holds against it — an end that is there is not the same
     * end as one that is not.
     */
    public abstract Optional<MatchedEndAttribution> matching(EndSide side, Endpoint target);

    /** What this holds on one side, for the questions inside this reading that have no end to
     *  compare against. */
    abstract Held heldAt(EndSide side);

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
     * <p>Which end survives is settled here; who is holding it is not. Each reading is asked
     * {@link #matching} about the end the meet arrived at, which is the same question the two
     * readings elsewhere ask — so the reading that lost is never asked on that side, and knowing
     * which one lost is what the ends had to be met for.
     */
    public final NarrowedBounds meet(NarrowedBounds other) {
        if (other == null) {
            return this;
        }
        NumericDomain.Bounds mine = bounds();
        NumericDomain.Bounds theirs = other.bounds();
        NumericDomain.Bounds met = mine == null ? theirs
                : theirs == null ? mine : mine.meet(theirs);
        if (met == null) {
            return NOTHING;
        }
        return read(met, held(met, other, EndSide.LOWER), held(met, other, EndSide.UPPER));
    }

    /**
     * The end {@code met} leaves on one side, with whichever readings are holding it.
     *
     * <p>Asked of both readings through the one operation the readings elsewhere use, so that the
     * end a name may be carried to is settled in one place and this is not a fourth answer to it.
     */
    private NarrowedEnd held(NumericDomain.Bounds met, NarrowedBounds other, EndSide side) {
        Endpoint end = side.at(met);
        if (end == null) {
            // Settled before either reading is compared, so that two readings with no end on this
            // side are not read as agreeing about one. There is no end here for anybody to hold.
            return null;
        }
        Optional<MatchedEndAttribution> mine = matching(side, end);
        Optional<MatchedEndAttribution> theirs = other.matching(side, end);
        if (mine.isEmpty()) {
            return new NarrowedEnd(end,
                    theirs.map(MatchedEndAttribution::held).orElse(Held.NONE));
        }
        if (theirs.isEmpty()) {
            return new NarrowedEnd(end, mine.get().held());
        }
        return new NarrowedEnd(end, Held.both(mine.get().held(), theirs.get().held()));
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
    public final boolean equals(Object other) {
        return other instanceof NarrowedBounds it && Objects.equals(bounds(), it.bounds())
                && names(EndSide.LOWER).equals(it.names(EndSide.LOWER))
                && names(EndSide.UPPER).equals(it.names(EndSide.UPPER));
    }

    @Override
    public final int hashCode() {
        return Objects.hash(bounds(), names(EndSide.LOWER), names(EndSide.UPPER));
    }

    @Override
    public final String toString() {
        return "NarrowedBounds[bounds=" + bounds() + ", minBy=" + names(EndSide.LOWER)
                + ", maxBy=" + names(EndSide.UPPER) + "]";
    }

    private List<TypeSymbol.AtModule> names(EndSide side) {
        return heldAt(side).names();
    }

    /** One of these where either side has an end, and the coordinate nothing stops where neither
     *  does. */
    private static NarrowedBounds read(NumericDomain.Bounds bounds, NarrowedEnd lower,
                                       NarrowedEnd upper) {
        return lower == null && upper == null ? NOTHING : new Reading(lower, upper);
    }

    /** Names written against an end, refused where there is no end to hold. */
    private static NarrowedEnd end(NumericDomain.Bounds bounds, EndSide side,
                                   List<TypeSymbol.AtModule> names) {
        Endpoint at = side.at(bounds);
        if (at != null) {
            return new NarrowedEnd(at, new Held(names));
        }
        // An absent end is not one a declaration moved. The rules leaving a coordinate everything on
        // one side is not a state any clause brought about, and a name held against it would be a
        // reader's licence to report an infinity as narrowed by somebody.
        if (!names.isEmpty()) {
            throw new IllegalArgumentException("no " + (side == EndSide.LOWER ? "lower" : "upper")
                    + " end to hold, and " + names + " named as holding it");
        }
        return null;
    }

    /** The same, with the work left to be done if anybody asks. */
    private static NarrowedEnd deferredEnd(NumericDomain.Bounds bounds, EndSide side,
                                           Supplier<List<TypeSymbol.AtModule>> names) {
        Endpoint at = side.at(bounds);
        return at == null ? null : new NarrowedEnd(at, new Held(names));
    }

    /** A coordinate no rule stops either way, which has no end for a declaration to be holding. */
    static final class Nothing extends NarrowedBounds {

        @Override
        public NumericDomain.Bounds bounds() {
            return null;
        }

        @Override
        public Optional<MatchedEndAttribution> matching(EndSide side, Endpoint target) {
            return Optional.empty();
        }

        @Override
        Held heldAt(EndSide side) {
            return Held.NONE;
        }
    }

    /**
     * A coordinate the rules stop one way or both, each end with what is holding it.
     *
     * <p>At least one end. A reading that stops the coordinate nowhere is {@link Nothing} and not
     * one of these with both sides missing: the two would be one thing said twice, and a caller
     * asking which it had would be asking a question with no consequence.
     */
    static final class Reading extends NarrowedBounds {

        private final NarrowedEnd lower;
        private final NarrowedEnd upper;

        Reading(NarrowedEnd lower, NarrowedEnd upper) {
            if (lower == null && upper == null) {
                throw new IllegalArgumentException(
                        "a reading that stops a coordinate nowhere is NOTHING");
            }
            this.lower = lower;
            this.upper = upper;
        }

        @Override
        public NumericDomain.Bounds bounds() {
            return new NumericDomain.Bounds(lower == null ? null : lower.endpoint(),
                    upper == null ? null : upper.endpoint());
        }

        @Override
        public Optional<MatchedEndAttribution> matching(EndSide side, Endpoint target) {
            NarrowedEnd end = at(side);
            return end == null || !end.endpoint().sameAs(target) ? Optional.empty()
                    : Optional.of(new MatchedEndAttribution(side, end.endpoint(), end.held()));
        }

        @Override
        Held heldAt(EndSide side) {
            NarrowedEnd end = at(side);
            return end == null ? Held.NONE : end.held();
        }

        /** Which end this is, read off which side of the reading it sits in and nowhere else. */
        private NarrowedEnd at(EndSide side) {
            return side == EndSide.LOWER ? lower : upper;
        }
    }
}
