package souther.compiler.partition;

import souther.compiler.meaning.Proposition;

import java.util.HashMap;
import java.util.Map;
import java.util.function.BooleanSupplier;
import java.util.function.Function;

/**
 * The way to each case a comparison's statement of several is asked in, and whether rows cross a
 * line in it, each worked out once however many lines of the statement ask.
 *
 * <p>Made for one comparison, because both answers are about the rows that reach it: the way to a
 * case is the way to the comparison with the case taken in beside it, and whether rows cross a line
 * in a case is asked of the arrivals and the reading of that comparison. The lines of a statement
 * of several are read over the same cases, and lines that part the same quantity at the same place
 * ask the same case for the same answer. What differs between lines is the cases each one holds,
 * and a case two of them hold is one question.
 *
 * <p>Whether rows cross is keyed by the line's {@link Cutting} and not by the line: two lines of
 * the statement reached along different arms of the choices before the comparison are two lines
 * and one cutting.
 */
final class WaysToACase {

    private final Function<Proposition, Reachability> reading;
    private final Map<Proposition, Reachability> ways = new HashMap<>();
    private final Map<Cutting, Map<Proposition, Boolean>> crossings = new HashMap<>();

    /**
     * @param reading the way to the comparison with a case taken in beside it
     */
    WaysToACase(Function<Proposition, Reachability> reading) {
        this.reading = reading;
    }

    /** The way to the comparison with {@code decides} taken in beside it. */
    Reachability apply(Proposition decides) {
        Reachability had = ways.get(decides);
        if (had == null) {
            had = reading.apply(decides);
            ways.put(decides, had);
        }
        return had;
    }

    /**
     * Whether rows cross the line {@code cutting} draws in the case {@code decides}, as {@code
     * asked} says the first time it is put.
     */
    boolean crossed(Cutting cutting, Proposition decides, BooleanSupplier asked) {
        Map<Proposition, Boolean> inCases = crossings.computeIfAbsent(cutting, _ -> new HashMap<>());
        Boolean had = inCases.get(decides);
        if (had == null) {
            had = asked.getAsBoolean();
            inCases.put(decides, had);
        }
        return had;
    }
}
