package souther.compiler.partition;

import souther.compiler.observe.Figure;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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

    /**
     * No row was found, and how the search ended; more than one where several runs looked.
     *
     * <p>Each way with the figures it was stopped at, as they stood where the search was compared
     * against them. None where the way is not a figure's, and none where the figure that stopped it
     * is one this compiler does not carry out as one: a figure is said where it is carried from
     * the place it was reached, and never worked out afterwards from which way it was.
     *
     * @param ended every way the search ended, in the order the ways are declared, each with the
     *              figures that stopped it there
     */
    record NoneFound(Map<Ended, List<Figure>> ended) implements ReplacementDisposition {

        public NoneFound {
            if (ended.isEmpty()) {
                throw new IllegalArgumentException("a search that found nothing ended some way");
            }
            Map<Ended, List<Figure>> copied = new EnumMap<>(Ended.class);
            ended.forEach((way, figures) -> copied.put(way, List.copyOf(figures)));
            ended = Collections.unmodifiableMap(copied);
        }

        /** A search that ended one way that no figure stopped. */
        public NoneFound(Ended one) {
            this(Map.of(one, List.of()));
        }

        /** The ways it ended, without the figures. */
        public Set<Ended> ways() {
            return ended.keySet();
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
        /** Nothing could run a row, or a row ran and nothing recorded what it did, so nothing could
         *  say what one answered. */
        NOTHING_RAN
    }

    /**
     * What two searches for one rewrite came to together: a row either found, or every way the
     * two ended, each with every figure either was stopped at there.
     */
    static ReplacementDisposition together(ReplacementDisposition one, ReplacementDisposition other) {
        if (one instanceof NoneFound(Map<Ended, List<Figure>> first)
                && other instanceof NoneFound(Map<Ended, List<Figure>> second)) {
            Map<Ended, Set<Figure>> both = new EnumMap<>(Ended.class);
            first.forEach((way, figures) ->
                    both.computeIfAbsent(way, _ -> new LinkedHashSet<>()).addAll(figures));
            second.forEach((way, figures) ->
                    both.computeIfAbsent(way, _ -> new LinkedHashSet<>()).addAll(figures));
            Map<Ended, List<Figure>> out = new EnumMap<>(Ended.class);
            both.forEach((way, figures) -> out.put(way, new ArrayList<>(figures)));
            return new NoneFound(out);
        }
        return one instanceof Witnessed ? one : other;
    }
}
