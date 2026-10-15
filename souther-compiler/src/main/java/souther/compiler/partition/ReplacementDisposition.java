package souther.compiler.partition;

import souther.compiler.observe.Figure;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.EnumMap;
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
     * <p>Each way with how it was met ({@link Met}): the figures it was stopped at, as they stood
     * where the search was compared against them, and whether it was met at something no figure
     * decides as well. A figure is said where it is carried from the place it was reached, and
     * never worked out afterwards from which way it was.
     *
     * @param ended every way the search ended, in the order the ways are declared, each with how
     *              it was met there
     */
    record NoneFound(Map<Ended, Met> ended) implements ReplacementDisposition {

        public NoneFound {
            if (ended.isEmpty()) {
                throw new IllegalArgumentException("a search that found nothing ended some way");
            }
            Map<Ended, Met> copied = new EnumMap<>(Ended.class);
            copied.putAll(ended);
            ended = Collections.unmodifiableMap(copied);
        }

        /** A search that ended one way that no figure stopped. */
        public NoneFound(Ended one) {
            this(Map.of(one, Met.AT_NO_FIGURE));
        }

        /** The ways it ended, without how. */
        public Set<Ended> ways() {
            return ended.keySet();
        }
    }

    /**
     * How a way of ending was met, over every time it was: the figures of this compiler's it was
     * stopped at, whether something no figure decides stopped it, and whether some meeting of it
     * was stopped by figures alone.
     *
     * <p>Three answers and not one. Two runs of one search can end alike, one at a figure and one
     * at the host's stack: told only the second, a reader would allow nothing more, and told only
     * the first, would be told nothing else stopped it. And a figure reached is not a figure a
     * wider run gets past: a run the first program answered nothing on cannot be told whatever
     * the second reached, so it reached its figure and leaves the way where it is. A wider run
     * gets past a way where one of its meetings was held by figures and by nothing else.
     *
     * @param figures             every figure it was stopped at, each once and in
     *                            {@link Figure#inOrder}
     * @param atNoFigure          whether something no figure decides stopped it as well
     * @param aWiderRunMayGetPast whether some meeting of it was stopped by figures alone
     */
    record Met(List<Figure> figures, boolean atNoFigure, boolean aWiderRunMayGetPast) {

        /** Met at nothing a figure decides, and at no figure. */
        public static final Met AT_NO_FIGURE = new Met(List.of(), true, false);

        public Met {
            figures = Figure.inOrder(figures);
            if (figures.isEmpty() && !atNoFigure) {
                throw new IllegalArgumentException(
                        "a way a search ended was met at a figure or at something else");
            }
            if (aWiderRunMayGetPast && figures.isEmpty()) {
                throw new IllegalArgumentException(
                        "a way a wider run gets past was stopped by a figure it raises");
            }
            if (!atNoFigure && !aWiderRunMayGetPast) {
                throw new IllegalArgumentException(
                        "a way stopped by nothing but figures is one a wider run gets past");
            }
        }

        /** Met once, at {@code figures} and nothing else. */
        public static Met at(Collection<? extends Figure> figures) {
            return new Met(List.copyOf(figures), false, true);
        }

        /**
         * Met once, at {@code figures} and, where {@code atNoFigure}, at something no figure
         * decides: a wider run gets past it only where that something is not there.
         */
        public static Met once(Collection<? extends Figure> figures, boolean atNoFigure) {
            return new Met(List.copyOf(figures), atNoFigure, !atNoFigure);
        }

        /** Both: every figure either was met at, something else where either was, and a wider
         *  run past it where it gets past either. */
        public Met and(Met other) {
            List<Figure> both = new ArrayList<>(figures);
            both.addAll(other.figures);
            return new Met(both, atNoFigure || other.atNoFigure,
                    aWiderRunMayGetPast || other.aWiderRunMayGetPast);
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
     * two ended, each met as either met it.
     */
    static ReplacementDisposition together(ReplacementDisposition one, ReplacementDisposition other) {
        if (one instanceof NoneFound(Map<Ended, Met> first)
                && other instanceof NoneFound(Map<Ended, Met> second)) {
            Map<Ended, Met> both = new EnumMap<>(Ended.class);
            both.putAll(first);
            second.forEach((way, met) -> both.merge(way, met, Met::and));
            return new NoneFound(both);
        }
        return one instanceof Witnessed ? one : other;
    }
}
