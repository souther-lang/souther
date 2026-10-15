package souther.compiler.partition;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Predicate;

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
 * <p><b>Held as the readings that put the place there, and owed to the lines they are of.</b> One
 * line the author wrote is read at as many places as calls put it: a helper's {@code x <= limit}
 * called with 12 in one arm and 24 in another is one line at two places, each put there by one
 * reading. Which places bound the runs beside a reading turns on which readings a row meets
 * together, so the readings are kept; what a run is owed to is the line, so that is what
 * {@link #alternatives} says.
 *
 * @param geometry where the values part
 * @param readings the readings of the lines the model wrote there, in the order they were read,
 *                 each of them enough on its own. Never empty
 */
public record Parting(Seam geometry, List<LineOrigin> readings) {

    public Parting {
        if (geometry == null) {
            throw new IllegalArgumentException("a parting is somewhere");
        }
        readings = List.copyOf(readings);
        if (readings.isEmpty()) {
            throw new IllegalArgumentException(
                    "the values part here because something parts them: " + geometry.spelled());
        }
    }

    /** One reading, where a producer is reading them one at a time. */
    public static Parting by(Seam geometry, LineOrigin reading) {
        return new Parting(geometry, List.of(reading));
    }

    /**
     * The lines the model wrote here, in the order their readings were read, each once: a rule
     * read twice is one rule, and what counts these is what says how many runs a row inside one of
     * them answers for.
     */
    public List<AuthoredLine> alternatives() {
        return readings.stream().map(LineOrigin::authoredLine).distinct().toList();
    }

    /** The same place, with the readings of {@code also} against it as well, each once. */
    public Parting and(Parting also) {
        List<LineOrigin> both = new ArrayList<>(readings);
        for (LineOrigin reading : also.readings) {
            if (!both.contains(reading)) {
                both.add(reading);
            }
        }
        return new Parting(geometry, both);
    }

    /**
     * The same place, put there only by the readings {@code kept} keeps — or empty where it keeps
     * none of them.
     */
    public Optional<Parting> putBy(Predicate<LineOrigin> kept) {
        List<LineOrigin> left = readings.stream().filter(kept).toList();
        return left.isEmpty() ? Optional.empty() : Optional.of(new Parting(geometry, left));
    }

    /** The same place said in units {@code per} times smaller, which is what a rule that wrote a
     *  multiple of the quantity divides in the quantity's own terms. Unheld where a number the place
     *  holds was not held in those units. */
    public ExactAnswer<Parting> scaledBy(ExactRatio per) {
        return geometry.scaledBy(per).map(scaled -> new Parting(scaled, readings));
    }

    /** What makes two of these one place, which is the quantity's answer and not the model's. */
    public String key() {
        return geometry.key();
    }
}
