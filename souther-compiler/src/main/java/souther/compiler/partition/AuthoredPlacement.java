package souther.compiler.partition;

import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * How the points of one reading of a line stand to the points of the line its author wrote.
 *
 * <p>Part of which reading this is, beside where it was read. One comparison read twice at one
 * place on one quantity can face its author's sides two ways: {@code x <= limit} handed {@code a}
 * holds below ten on {@code a}, and handed {@code 20 - a} holds above it. The two readings stand at
 * the same line on the input, and the run below it is the author's holding side in one and the
 * other side in the other — so a reading told apart by the place alone puts what a row showed
 * about one of the author's points under another. Where the two face the author's line alike they
 * are one reading, whatever else differs between them.
 *
 * <p>Worked out once, by the border ({@link Border#placement}), and read by everything that asks
 * where a reading's point is on the author's line: what the reading owes, what it holds open, and
 * which readings are one.
 */
public sealed interface AuthoredPlacement {

    /** A line a declaration drew, read in the type's own values: each point is the line's own. */
    record ItsOwn() implements AuthoredPlacement {}

    /**
     * A reading shown to be a place of the author's line.
     *
     * @param points each of the reading's own points, and the author's point it is — or nothing
     *               where the reading cannot tell which of the author's sides it is on
     */
    record Placed(Map<DomainPoint, Optional<DomainPoint>> points) implements AuthoredPlacement {

        public Placed {
            points = Map.copyOf(Objects.requireNonNull(points, "a reading has points"));
        }

        /** The author's point the reading's {@code point} is, or nothing where it is not tied. */
        public Optional<DomainPoint> of(DomainPoint point) {
            Optional<DomainPoint> tied = points.get(point);
            if (tied == null) {
                throw new IllegalArgumentException("not a point of this reading: " + point);
            }
            return tied;
        }
    }

    /** A reading shown to be no place of the author's line: a caller's choice between values the
     *  comparison comes out one way for. */
    record NoPlaceOfTheLine() implements AuthoredPlacement {}

    /** A reading not shown to be a place of the author's line or not to be one: a caller's choice
     *  turns the comparison where this reading has a line. */
    record NotShown() implements AuthoredPlacement {}
}
