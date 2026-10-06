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
    record Witnessed(RowId witness) implements ReplacementDisposition {

        public Witnessed {
            Objects.requireNonNull(witness, "a row found is some row");
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
        /** The search had made as many runs as the measure lets one rewrite take, with rows it had
         *  not tried ({@link AdequacyPolicy.OfTheMeasures#rewriteRuns}). */
        RUNS_A_REWRITE_MAY_TAKE,
        /** Composing the rows it looked through stopped at a figure of its own, with assignments
         *  it had not composed. */
        A_FIGURE_OF_THE_COMPOSING,
        /** A run the search asked for did not come back with an answer: it ran past what a run may
         *  spend, or the rewrite could not be run. */
        A_RUN_DID_NOT_COME_BACK,
        /** The block the row would have gone in held as many rows as a block may. Only ever of a
         *  search for the rows handed a person ({@link RewriteSearch.For#THE_BLOCK}). */
        ROWS_A_BLOCK_MAY_HOLD,
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
