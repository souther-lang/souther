package souther.compiler.partition;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * One total a rule cuts at several places: the value computed from several positions, and the
 * comparison the author wrote that holds it against thresholds.
 *
 * <p>The comparison is the author's, and not the quantity alone. Two comparisons that happen to
 * cut the same direction are two computations that can each be wrong in their own weights, so they
 * are two families; one comparison read against every row of a table is one computation and one
 * family however many thresholds the table has. A comparison written in a body carries no level in
 * its identity ({@link BorderObligationId}), which is what makes a table's rows one line.
 *
 * <p>A family exists only where the total is cut at more than one place. Cut at one, the values of
 * a position that settle the comparison are the same outcome throughout, and that is what the
 * position's class says; cut at several, a value that settles one threshold leaves the next either
 * way, and the outcome is no longer the same through the class. What the family owes in the place
 * of those classes is asked of the family, so that what is no longer divided and what is owed
 * instead are decided from one value.
 *
 * @param line       the comparison the author wrote
 * @param expression the direction of the total, which is what its weights are weights of
 */
public record DerivedFamily(AuthoredLine line, QuantityKey expression) {

    /** The family a line drawn on {@code of} by {@code by} is a threshold of, where {@code of} is a
     *  total. */
    public static Optional<DerivedFamily> of(LineOrigin by, BorderQuantity of) {
        return of.totalOfSeveralPositions()
                .map(expression -> new DerivedFamily(by.authoredLine(), expression));
    }

    /** Where one threshold of a family is: the family and the place on the total. */
    record Threshold(DerivedFamily family, QuantityCut at) {}

    /** Every family cut at more than one of the places given. */
    static Set<DerivedFamily> cutAtSeveralPlaces(List<Threshold> thresholds) {
        Map<DerivedFamily, Set<QuantityCut>> places = new HashMap<>();
        for (Threshold each : thresholds) {
            places.computeIfAbsent(each.family(), _ -> new HashSet<>()).add(each.at());
        }
        Set<DerivedFamily> out = new HashSet<>();
        places.forEach((family, at) -> {
            if (at.size() > 1) {
                out.add(family);
            }
        });
        return out;
    }

    /** The family a border is one threshold of, where it cuts a total. */
    public static Optional<DerivedFamily> of(Border border) {
        return of(border.origin(), border.cut().of());
    }

    /** Every family cut at more than one of the places the borders given are at. */
    public static Set<DerivedFamily> cutAtSeveralPlacesBy(List<Border> borders) {
        List<Threshold> thresholds = new ArrayList<>();
        for (Border each : borders) {
            of(each).ifPresent(family -> thresholds.add(
                    new Threshold(family, each.cut().cut().canonical())));
        }
        return cutAtSeveralPlaces(thresholds);
    }

    /** The threshold a line drawn between positions is, where it is one of a total. */
    static Optional<Threshold> thresholdOf(LineDrawn drawn) {
        return of(drawn.by(), drawn.cuts().of())
                .map(family -> new Threshold(family, drawn.cuts().target().cut().canonical()));
    }
}
