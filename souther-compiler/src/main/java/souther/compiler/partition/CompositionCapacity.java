package souther.compiler.partition;

import souther.compiler.observe.RunSensitivity;

import java.util.ArrayList;
import java.util.List;

/**
 * A number a search worked out and could not hold, named by what it was working out and by whether a
 * run with more room would have held it.
 *
 * <p><b>Apart from {@link CompositionBudget} and {@link CompositionRepertoire}, and the difference
 * is again what a reader can do.</b> A figure is raised and the search goes on; a population this
 * compiler writes some of is reached by somebody writing the rest. Neither reaches a number this
 * compiler could not hold: no figure stopped the search, and the next value it would have tried is
 * one it has a way of naming. What reaches it is either a run with more room or nothing at all,
 * which is the half of this that {@link UnheldNumber} says, and the two answer
 * {@link #runSensitivity} oppositely.
 *
 * <p>So it travels as a third vocabulary beside the other two and is never folded into either.
 * Folded into a figure, a reader raises a number that reaches nothing; folded into a population,
 * they are told somebody has to write something when what ran out was the arithmetic.
 */
public record CompositionCapacity(Where where, UnheldNumber why) {

    public CompositionCapacity {
        if (where == null || why == null) {
            throw new IllegalArgumentException(
                    "a number not held says what was being worked out and why it was not held");
        }
    }

    /** What a search was working out when the number was one it could not hold. */
    public enum Where {

        /** The next place out along a line two positions are tried standing at. */
        PLACES_A_PAIR_IS_WALKED_TO,

        /** The place a distance between two positions moves one of them to, once the other is
         *  placed. */
        PLACES_A_DISTANCE_MOVES_A_POSITION_TO,

        /** The next value of a progression a form's last position is walked along. */
        VALUES_OF_A_PROGRESSION_WALKED_TO,

        /** The next value a position is walked to on the way to a condition. */
        VALUES_A_POSITION_ON_THE_WAY_IS_WALKED_TO
    }

    /** Whether measuring again, allowing more, could hold the number. */
    public RunSensitivity runSensitivity() {
        return why.runSensitivity();
    }

    /** Every one there is, which is what an order over them has to hold. */
    public static List<CompositionCapacity> every() {
        List<CompositionCapacity> out = new ArrayList<>();
        for (Where where : Where.values()) {
            for (UnheldNumber why : UnheldNumber.values()) {
                out.add(new CompositionCapacity(where, why));
            }
        }
        return out;
    }
}
