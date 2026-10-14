package souther.compiler.partition;

import java.util.Objects;

/**
 * Where one reading of a line stands with respect to a point of the line it is owed for: at one of
 * its own points, or nowhere this reading can say.
 *
 * <p>Two values because the point is the author's and the reading's places are the reading's. A
 * line a declaration drew is read in the type's own values, so every reading of one of its points
 * stands at that point. A comparison a body wrote is read once per call, each on the quantity the
 * call put the comparison on, so the same point of the author's line is a different place in each:
 * where {@code x} meets ten is {@code a = 10} in one call and {@code b = 20} in another. What a row
 * at the point is asked for is asked at the reading's own place, and what one reading of a point
 * came to is that reading's place's answer.
 *
 * <p>And a reading can be of the line without being shown to stand at any of its points. One shown
 * to be a place of the author's line whose sides it cannot tell apart is {@link Untied}; one where a
 * caller's choice decides the comparison is not shown to be a place of the line at all, and is
 * {@link Unresolved}. Either is evidence the reading holds about the point and cannot settle, which
 * a point said to be met or missed on its account would be overstating. Only the first is evidence
 * that the point is owed: a point no reading but an unresolved one names is no point of the debt.
 */
public sealed interface ReadingSeat {

    /** The point of the reading's own line it was asked at. */
    DomainPoint asked();

    /** At {@code asked}, which is the point of the author's line. */
    record At(DomainPoint asked) implements ReadingSeat {

        public At {
            Objects.requireNonNull(asked, "a reading stands at some point of its line");
        }
    }

    /**
     * Asked at {@code asked}, which this reading cannot tie to the point of the author's line it is
     * filed under.
     */
    record Untied(DomainPoint asked) implements ReadingSeat {

        public Untied {
            Objects.requireNonNull(asked, "a reading is asked at some point of its line");
        }
    }

    /**
     * Asked at {@code asked}, which this reading is not shown to be a place of the author's line
     * at all.
     */
    record Unresolved(DomainPoint asked) implements ReadingSeat {

        public Unresolved {
            Objects.requireNonNull(asked, "a reading is asked at some point of its line");
        }
    }

    /**
     * The one of {@code one} and {@code other}, two seats of one reading at one point, that says
     * the most about where the reading stands.
     */
    static ReadingSeat closer(ReadingSeat one, ReadingSeat other) {
        return rank(other) > rank(one) ? other : one;
    }

    private static int rank(ReadingSeat seat) {
        return switch (seat) {
            case At _ -> 2;
            case Untied _ -> 1;
            case Unresolved _ -> 0;
        };
    }
}
