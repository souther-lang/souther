package souther.compiler.meaning;

import java.util.ArrayList;
import java.util.List;

/**
 * The rows on which a run stops in a comparison that is read once on each application of a closure,
 * or once where it is made on none.
 *
 * <p>Joined here and not by whoever reads the comparison: a proposition is made where a rule
 * concludes it, and what a stop on one application comes to for the comparison is the rule that
 * says a run that never makes the application is not stopped by it.
 */
public final class WhereARunStops {

    private WhereARunStops() {
    }

    /**
     * One reading of the comparison.
     *
     * @param reached where the application is made, or null for a comparison read once and made
     *                wherever it stands
     * @param meaning what the comparison states there, and how that was derived
     */
    public record OnOneReading(Proposition reached, MeaningsOfABody.Meaning meaning) {

        public OnOneReading {
            if (meaning == null) {
                throw new IllegalArgumentException("a reading of a comparison states something");
            }
        }
    }

    /** The rows a run stops on across {@code readings}, or null where none stops. */
    public static Proposition across(List<OnOneReading> readings) {
        List<Proposition> stops = new ArrayList<>();
        for (OnOneReading one : readings) {
            Proposition here = one.meaning().whereARunStops();
            if (here != null) {
                stops.add(one.reached() == null ? here
                        : Proposition.all(List.of(one.reached(), here)));
            }
        }
        return stops.isEmpty() ? null : Proposition.any(stops);
    }
}
