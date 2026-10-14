package souther.compiler.partition;

import java.util.List;
import java.util.Objects;

/**
 * A point of a line no row is owed at, as what tells it from every other.
 *
 * <p>The counterpart of {@link BorderObligationPoint} for the points nothing is asked of, and told
 * apart the same way: by the line, where on it, and where whatever else settled it stands. The run
 * above a type's bound holds values where nothing else stops it, and is empty where a record's
 * clause holds the field at the bound; the point there is owed in the first place and not in the
 * second, and the second is told from the first by where the run stops. Who stopped it there is
 * whose the point is, and is the answer read beside this ({@link LeftOutPoint#attribution}) rather
 * than part of it, for the reason it is beside a {@link BorderObligationPoint}: two readings can
 * name the declarations behind one place differently and are still one point.
 *
 * <p>Equal over the places as a set. Which of them a reading met first is the order its
 * arrangement was walked in, and an identity that read the order would make two readings of one
 * point two points.
 *
 * @param line   the line
 * @param point  where on the quantity
 * @param reason why no row is owed there
 * @param stops  where else it was settled: the far end of the empty run beside the line, or the
 *               ends the rules leave the position at that refuse the value. None where the line
 *               alone settled it, or where the carrier names no value there
 */
public record NotOwedPoint(BorderObligationId line, DomainPoint point, NotOwedReason reason,
                           List<FarEnd> stops) {

    public NotOwedPoint {
        if (line == null || point == null || reason == null) {
            throw new IllegalArgumentException("a point no row is owed at is some line's, somewhere"
                    + " on it, for a reason: " + line + " " + point + " " + reason);
        }
        stops = List.copyOf(stops);
    }

    /** Equal where the places are the same places, in whatever order each reading met them. Each
     *  place is there once ({@link RegionClaim#byBasis}), so holding each other's is being the same
     *  set. */
    @Override
    public boolean equals(Object other) {
        return other instanceof NotOwedPoint that && line.equals(that.line)
                && point.equals(that.point) && reason == that.reason
                && stops.size() == that.stops.size() && stops.containsAll(that.stops);
    }

    /** Summed over the places, which is the same in every order they come in. */
    @Override
    public int hashCode() {
        return Objects.hash(line, point, reason,
                stops.stream().mapToInt(FarEnd::hashCode).sum());
    }
}
