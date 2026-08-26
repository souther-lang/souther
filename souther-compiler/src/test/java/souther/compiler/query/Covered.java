package souther.compiler.query;

import java.util.List;

/**
 * What something that looks for defects came to: what it found, and whether that is all there is.
 *
 * <p>Two arms and no accessor above them. Every walk here narrows what it looks at — a bound on how
 * far it goes, a field the runtime will not open, a graph that holds itself, two containers whose
 * members will not line up, a class that will not load, a question only one of two stores was put —
 * and a caller that read the findings without meeting the narrowing would hold a register against a
 * search that covered less than the register names. Written as a pair of fields, that reading is one
 * an author has to remember not to take; written as two arms, it is one they cannot spell.
 *
 * <p>Which is why {@link Whole} and {@link Partly} share nothing. An interface with {@code found()}
 * on it is the pair of fields again with a longer name.
 */
sealed interface Covered<T> {

    /** Everything there was to look at was looked at, and this is what was found. */
    record Whole<T>(List<T> found) implements Covered<T> {}

    /** This is what was found, and here is where the looking fell short. */
    record Partly<T>(List<T> found, List<Gap> gaps) implements Covered<T> {}

    /** Whichever of the two {@code gaps} makes this. */
    static <T> Covered<T> of(List<T> found, List<Gap> gaps) {
        return gaps.isEmpty() ? new Whole<>(List.copyOf(found))
                : new Partly<>(List.copyOf(found), List.copyOf(gaps));
    }
}
