package souther.compiler.partition;

import java.util.ArrayList;
import java.util.List;

/**
 * One place a quantity's values part, and the lines the model wrote there.
 *
 * <p>Two questions, and they are not one. Where the values part is the quantity's
 * ({@link Seam}), which is why two rules cutting at one number divide it once. Which rules put a
 * line there is the model's, and a rule is something an author can move without touching the one
 * beside it — so a place divides once and can have been written more than once.
 *
 * <p><b>Alternatives and not one cause.</b> Each of these is enough on its own to part the values
 * here: a declaration stopping a minute at 1000 and a body comparing against the same 1000 each do
 * it, and taking one of the two away leaves the place where it is. Held as one set of contributors,
 * adding a second line that changes nothing about the quantity would change what the first one is —
 * so they are kept apart, and whoever asks what a run is owed to asks about each of them.
 *
 * <p>Where the values part is settled once, by the arrangement of the quantity
 * ({@link QuantityArrangement}). Each producer of lines hands its candidates over as they are read;
 * two candidates at one place come back as one place with both lines against it.
 *
 * @param geometry     where the values part
 * @param alternatives the lines the model wrote there, in the order they were read, each of them
 *                     enough on its own. Never empty
 */
public record Parting(Seam geometry, List<AuthoredLine> alternatives) {

    public Parting {
        if (geometry == null) {
            throw new IllegalArgumentException("a parting is somewhere");
        }
        alternatives = List.copyOf(alternatives);
        if (alternatives.isEmpty()) {
            throw new IllegalArgumentException(
                    "the values part here because something parts them: " + geometry.key());
        }
    }

    /** One line, where a producer is reading them one at a time. */
    public static Parting by(Seam geometry, AuthoredLine line) {
        return new Parting(geometry, List.of(line));
    }

    /**
     * The same place, with the lines of {@code also} against it as well.
     *
     * <p>One entry per line: a rule read twice is one rule, and what counts these is what says how
     * many runs a row inside one of them answers for.
     */
    public Parting and(Parting also) {
        List<AuthoredLine> both = new ArrayList<>(alternatives);
        for (AuthoredLine line : also.alternatives) {
            if (!both.contains(line)) {
                both.add(line);
            }
        }
        return new Parting(geometry, both);
    }

    /** The same place said in units {@code per} times smaller, which is what a rule that wrote a
     *  multiple of the quantity divides in the quantity's own terms. */
    public Parting scaledBy(java.math.BigDecimal per) {
        return new Parting(geometry.scaledBy(per), alternatives);
    }

    /** What makes two of these one place, which is the quantity's answer and not the model's. */
    public String key() {
        return geometry.key();
    }

    /** The same place with every level written the one way, for an identity to be built from. */
    public Parting canonical() {
        return new Parting(geometry.canonical(), alternatives);
    }
}
