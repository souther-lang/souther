package souther.compiler.partition;

import souther.compiler.check.NarrowedBounds;
import souther.compiler.numeric.EndSide;
import souther.compiler.numeric.NumericDomain;

import java.util.EnumMap;
import java.util.Map;
import java.util.function.Function;

/**
 * Both ends of what the rules leave a quantity, each under the side it is.
 *
 * <p>Here so that choosing a side happens once. Where the two ends are two arguments, everything
 * that goes into one of them — which end of the range to read, which way the run lies from it, which
 * of a reading's two answers is about it — is chosen again at every place they are built or passed
 * on, and a slip in any one of those puts one end's answer beside the other's.
 *
 * <p>So the side is never handed in. {@link #leaving} walks the two sides itself and asks for the
 * end at each, and what comes back is filed under the side it was asked for. A caller cannot label
 * an end because it never says a label; it only answers a question that already names one.
 */
public final class DomainEnds {

    /** A quantity the rules stop neither way. */
    static final DomainEnds NONE = new DomainEnds(Map.of());

    private final Map<EndSide, DomainEnd> byEnd;

    private DomainEnds(Map<EndSide, DomainEnd> byEnd) {
        this.byEnd = byEnd;
    }

    /**
     * What {@code reach} leaves the quantity either way, with whatever {@code narrowed} answers
     * about each of those ends.
     *
     * <p>The one way a pair of these is made with names on it. Both ends come from one walk of the
     * sides, so which end a reading was asked about and which end the answer is written beside are
     * the same choice made once.
     *
     * @param like the level the quantity's places are written as
     */
    static DomainEnds leaving(LevelSpace space, Level like, NumericDomain.Bounds reach,
                              NarrowedBounds narrowed) {
        return of(side -> DomainEnd.leaving(space, like, reach, side, narrowed));
    }

    /** The ends {@code each} answers with, filed under the side each was asked about. */
    static DomainEnds of(Function<EndSide, DomainEnd> each) {
        Map<EndSide, DomainEnd> out = new EnumMap<>(EndSide.class);
        for (EndSide side : EndSide.values()) {
            DomainEnd end = each.apply(side);
            if (end == null) {
                continue;
            }
            if (end.side() != side) {
                // Asked about one end and answered about the other, which nothing below could tell
                // from the right answer: at a quantity holding one value the two lower to one place.
                throw new IllegalArgumentException(
                        "an end of the " + end.side() + " answered for " + side);
            }
            out.put(side, end);
        }
        return out.isEmpty() ? NONE : new DomainEnds(out);
    }

    /** The end on one side, or null where the rules leave the quantity everything that way. */
    DomainEnd at(EndSide side) {
        return byEnd.get(side);
    }

    /** Where the quantity stops on one side, or null where nothing does. */
    Bound boundAt(EndSide side) {
        return DomainEnd.boundOf(at(side));
    }
}
