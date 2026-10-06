package souther.compiler.partition;

import java.util.EnumSet;
import java.util.Objects;
import java.util.Set;

/**
 * What a search for a row that tells a rewrite of the body from the body came to.
 *
 * <p>Two answers and not a row that may be missing. A row found is an input on which the rewrite
 * answers differently, and that is the whole of what it shows. None found is never that the rewrite
 * answers alike everywhere — what the search did not look at, it says nothing about — so it says
 * which of the ways a search ends this one ended in.
 */
public sealed interface ReplacementDisposition {

    /** A row the rewrite answers differently on, composed and run. */
    record Witnessed(RowId row) implements ReplacementDisposition {

        public Witnessed {
            Objects.requireNonNull(row, "a row found is some row");
        }
    }

    /** No row was found, and how the search ended; more than one where several runs looked. */
    record NoneFound(Set<Ended> ended) implements ReplacementDisposition {

        public NoneFound {
            if (ended.isEmpty()) {
                throw new IllegalArgumentException("a search that found nothing ended some way");
            }
            ended = Set.copyOf(EnumSet.copyOf(ended));
        }

        public NoneFound(Ended one) {
            this(Set.of(one));
        }
    }

    /** How a search that found nothing ended. */
    enum Ended {
        /** Rows were composed and run, and the rewrite answered each of them as the body does. */
        EVERY_ROW_ANSWERED_ALIKE,
        /** No row the search could look at was composed: the values were refused, or the way to
         *  where it had to look was not one this could write. */
        NOTHING_WAS_COMPOSED,
        /** The search stopped with rows it had not tried. */
        THE_SEARCH_STOPPED,
        /** Nothing could run a row, so nothing could say what one answered. */
        NOTHING_RAN
    }

    /**
     * What two searches for one rewrite came to together: a row either found, or every way the
     * two ended.
     */
    static ReplacementDisposition together(ReplacementDisposition one, ReplacementDisposition other) {
        if (one instanceof NoneFound(Set<Ended> first)
                && other instanceof NoneFound(Set<Ended> second)) {
            Set<Ended> both = EnumSet.noneOf(Ended.class);
            both.addAll(first);
            both.addAll(second);
            return new NoneFound(both);
        }
        return one instanceof Witnessed ? one : other;
    }
}
