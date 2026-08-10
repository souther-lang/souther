package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The two promises about a count, kept apart.
 *
 * <p>A caller with a line drawn at a count needs that count; a caller with a floor to clear needs a
 * value above it. The second is answered by asking for the first today, and the point of writing them
 * as two is that it need not stay that way. Held here rather than through the report, because a size
 * larger than a row is worth carrying is one the measure calls undecided before the generator is
 * asked, so the report has no way to show which half of the answer was given.
 */
class WhatBuildsASizeSaysWhatItCouldNotBuildTest {

    private static final Symbols NONE = Symbols.none();

    @Test
    void aStringOfTheSizeAskedForIsBuilt() {
        assertEquals(List.of("\"xxx\""),
                Witnesses.ofSize(Type.STRING, 3, NONE, Set.of()).stream()
                        .map(FixtureTemplate::text).toList());
    }

    /**
     * A count of none is the empty value and not the absence of an answer.
     *
     * <p>A line drawn at zero is an edge a row stands on, and the empty string is what stands there.
     */
    @Test
    void aSizeOfZeroIsTheEmptyValue() {
        assertEquals(List.of("\"\""),
                Witnesses.ofSize(Type.STRING, 0, NONE, Set.of()).stream()
                        .map(FixtureTemplate::text).toList());
        assertEquals(List.of("[]"),
                Witnesses.ofSize(new Type.ListOf(Type.INT), 0, NONE, Set.of()).stream()
                        .map(FixtureTemplate::text).toList());
    }

    /**
     * A floor of none asks for no value in particular.
     *
     * <p>Where the two promises come apart. A rule saying a collection holds at least nothing has said
     * nothing about the value, and the position's own chooser answers; a line at zero is a place a row
     * is owed at. One method cannot mean both, which is why there are two.
     */
    @Test
    void aFloorOfNoneAsksForNothingWhereASizeOfZeroAsksForTheEmptyValue() {
        assertEquals(List.of(), Witnesses.holding(Type.STRING, 0, NONE, Set.of()));
        assertTrue(!Witnesses.ofSize(Type.STRING, 0, NONE, Set.of()).isEmpty());
    }

    /** A count past what a row is worth carrying is one nothing composes, and says which it is. */
    @Test
    void aSizeNoRowWouldCarrySaysNothingComposesOne() {
        assertEquals(List.of(), Witnesses.ofSize(Type.STRING, 100_000, NONE, Set.of()));
        assertEquals(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                Witnesses.reasonForSize(Type.STRING, 100_000, NONE));
    }

    /** A carrier nothing counts has no size to build at, and that is not a limit being reached. */
    @Test
    void aCarrierNothingCountsHasNoReasonToGive() {
        assertEquals(List.of(), Witnesses.ofSize(Type.INT, 3, NONE, Set.of()));
        assertEquals(null, Witnesses.reasonForSize(Type.INT, 3, NONE));
    }
}
