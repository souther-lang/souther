package souther.compiler.check;

import souther.compiler.numeric.EndSide;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * What a reading of a value left one of its positions, and who is holding an end of it, for tests
 * outside this package.
 *
 * <p>Here and not on {@link NarrowedBounds} because only a reading writes one of those down, and
 * only against an end does it say who holds it. A compiler-side factory pairing ends with names
 * would let one reading's ends be paired with another reading's names, and a compiler-side reader
 * taking the names alone would let them be written beside a stranger's end — which are the two
 * states the type exists to make unwritable. So the way a test reaches either is a seam in this
 * package rather than API the compiler ships.
 */
public final class AReadingOfAPosition {

    /** A position stopping at {@code at} on the high side, with {@code by} holding that end. */
    public static NarrowedBounds withAnUpperEndAt(Endpoint at, TypeSymbol.AtModule... by) {
        return NarrowedBounds.of(new NumericDomain.Bounds(null, at), List.of(), List.of(by));
    }

    /** The same on the low side. */
    public static NarrowedBounds withALowerEndAt(Endpoint at, TypeSymbol.AtModule... by) {
        return NarrowedBounds.of(new NumericDomain.Bounds(at, null), List.of(by), List.of());
    }

    /**
     * Who is holding the end {@code narrowed} leaves on one side.
     *
     * <p>Asked with that end, because that is the only way to ask. What a reading holds is about the
     * number it arrived at, so a caller wanting the names says which number it means — and a test
     * asking about the reading's own answer means this one.
     */
    public static List<TypeSymbol.AtModule> holding(NarrowedBounds narrowed, EndSide side) {
        return narrowed.matching(side, side.at(narrowed.bounds()))
                .map(MatchedEndAttribution::names).orElseGet(List::of);
    }

    private AReadingOfAPosition() {}
}
