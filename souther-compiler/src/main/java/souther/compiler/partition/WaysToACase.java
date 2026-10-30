package souther.compiler.partition;

import souther.compiler.collect.LatelyAsked;
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
 *
 * <p>A way is kept while it is among the {@link #CASES_KEPT} asked last, and not for as long as the
 * comparison is read. Each is a reading of the whole region with the case taken in, and a statement
 * of several is asked in thousands of cases; the lines asking one case are read one after another,
 * so a way is asked again soon after it was worked out or not at all. One asked again after it was
 * let go is worked out again, and is the way it was.
 */
final class WaysToACase {

    /**
     * How many cases' ways are kept, and what each case puts on the way: more than the cases the
     * lines asking one case put in between in the models measured, so none of those is worked out
     * twice there.
     */
    static final int CASES_KEPT = 512;

    private final Function<Proposition, Reachability> reading;
    private final LatelyAsked<Proposition, Reachability> ways = new LatelyAsked<>(CASES_KEPT);
    private final Map<Cutting, Map<Proposition, Boolean>> crossings = new HashMap<>();

    /**
     * @param reading the way to the comparison with a case taken in beside it
     */
    WaysToACase(Function<Proposition, Reachability> reading) {
        this.reading = reading;
    }

    /** The way to the comparison with {@code decides} taken in beside it. */
    Reachability apply(Proposition decides) {
        return ways.answer(decides, reading);
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
