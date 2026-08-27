package souther.compiler.partition;

import souther.compiler.numeric.EndSide;

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
 * <p>So the side is never handed in. {@link #of} walks the two sides itself and asks for the end at
 * each, and what comes back is filed under the side it was asked for. A caller cannot label an end
 * because it never says a label; it only answers a question that already names one.
 *
 * @param byEnd the end at each side, absent where the rules leave the quantity everything that way
 */
record DomainEnds(Map<EndSide, DomainEnd> byEnd) {

    /** A quantity the rules stop neither way. */
    static final DomainEnds NONE = new DomainEnds(Map.of());

    DomainEnds {
        byEnd.forEach((side, end) -> {
            if (end.side() != side) {
                throw new IllegalArgumentException(
                        "an end of the " + end.side() + " filed under " + side);
            }
        });
        byEnd = Map.copyOf(byEnd);
    }

    /** The ends {@code each} answers with, filed under the side each was asked about. */
    static DomainEnds of(Function<EndSide, DomainEnd> each) {
        Map<EndSide, DomainEnd> out = new EnumMap<>(EndSide.class);
        for (EndSide side : EndSide.values()) {
            DomainEnd end = each.apply(side);
            if (end != null) {
                out.put(side, end);
            }
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
