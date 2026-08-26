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
    record Whole<T>(List<T> found) implements Covered<T> {

        public Whole {
            found = List.copyOf(found);
        }
    }

    /**
     * This is what was found, and here is where the looking fell short.
     *
     * <p>Something fell short or this is not what happened. Built with nothing in {@code gaps}, it
     * says a search covered less than everything and names nowhere it stopped — and a caller that
     * met the arm and added its gaps to a list would come away with the list unchanged, which is the
     * reading the two arms exist to make impossible.
     */
    record Partly<T>(List<T> found, List<Gap> gaps) implements Covered<T> {

        public Partly {
            found = List.copyOf(found);
            gaps = List.copyOf(gaps);
            if (gaps.isEmpty()) {
                throw new IllegalArgumentException(
                        "a search that fell short says where: " + found.size() + " found");
            }
        }
    }

    /** Whichever of the two {@code gaps} makes this. */
    static <T> Covered<T> of(List<T> found, List<Gap> gaps) {
        return gaps.isEmpty() ? new Whole<>(List.copyOf(found))
                : new Partly<>(List.copyOf(found), List.copyOf(gaps));
    }
}
