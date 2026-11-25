package souther.compiler.partition;

import java.util.EnumSet;
import java.util.Set;

/**
 * What looking for one row may spend, over every attempt made for it.
 *
 * <p>A row for a point, a rule or a case is looked for many times over: along each way the point
 * is looked along, at each value it is tried with, for each pair of the input's numbers and each
 * way of standing the dependencies in, and in each walk across the row's parameters those make.
 * Each of those is bounded, and their number is not, so a figure made afresh in any of them bounds
 * one of them and not the looking. The figures the looking is to be bounded by are held here
 * instead, made once by whoever starts looking for the row and handed to every attempt for it:
 * splitting the looking is no way past them.
 *
 * <p><b>And which of them left something undone, over any stretch of the looking.</b> Whatever
 * puts together what several attempts came to — the first value's answer, the nearest pair, a
 * proof over every way — asks this over the stretch it put together ({@link #from},
 * {@link Mark#leftAt}), and says what it is told as an outcome of its own beside the ones it
 * chose. Written onto one of those instead, it is lost with every one the choosing passes over,
 * and a proof over the ones kept is taken for a proof over what was never looked at. Asked here
 * and not read off the attempts, so an attempt that ran out inside itself, the last one allowed
 * included, is told as surely as one that was never made.
 *
 * <p><b>Only a figure whose composing nothing else bounds is held here.</b> A figure of one walk
 * whose every unit is also a search of the looking's — the rows a walk hands a preference, each
 * of which the walk goes on to as one of {@link #searches} — is bounded over the looking by those
 * searches already, and held here as well it would only take from each walk what another spent,
 * so that fewer rows were tried at a point and the bound on the looking was no tighter.
 *
 * <p>Which looking a row is is the caller's to say, and nothing here works it out. A caller that
 * makes one of these for each attempt has the figures of an attempt, which is what they were
 * before this held them.
 */
public final class LookingForARow {

    private final Tries searches;
    private final Tries composedOnTheWay =
            new Tries(CompositionBudget.ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR.maximum());

    /** Looking for a row under the figures as declared. */
    public LookingForARow() {
        this(CompositionBudget.SEARCHES_A_ROW_IS_COMPOSED_THROUGH.maximum());
    }

    /** The same, the walks across the row's parameters held to {@code searches} searches. */
    LookingForARow(int searches) {
        this.searches = new Tries(searches);
    }

    /** Where the looking stands now, for asking afterwards what it left undone since. */
    public Mark from() {
        return new Mark(searches.refusals(), composedOnTheWay.refusals());
    }

    /** A point in the looking, from which what it left undone is asked. */
    public final class Mark {

        private final int searchesRefused;
        private final int composedRefused;

        private Mark(int searchesRefused, int composedRefused) {
            this.searchesRefused = searchesRefused;
            this.composedRefused = composedRefused;
        }

        /** The figures the looking left something undone at since this mark, and none where it
         *  left nothing. */
        public Set<CompositionBudget> leftAt() {
            Set<CompositionBudget> out = EnumSet.noneOf(CompositionBudget.class);
            if (searches.refusals() > searchesRefused) {
                out.add(CompositionBudget.SEARCHES_A_ROW_IS_COMPOSED_THROUGH);
            }
            if (composedOnTheWay.refusals() > composedRefused) {
                out.add(CompositionBudget.ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR);
            }
            return out;
        }
    }

    /**
     * Whether there is a search left for one more attempt, asked by whatever makes the attempts
     * before it makes the next ({@link Tries#left}). Where there is none, the looking is cut short
     * there, and the attempt is not made.
     */
    public boolean left() {
        return searches.left();
    }

    /**
     * Whether one more attempt is made: a search is spent on it where one is left, and where none
     * is, the looking is cut short there. For an attempt that is not a composing of its own, which
     * spends where it starts ({@link Generator#probeFixing}).
     */
    public boolean attempt() {
        return searches.spend();
    }

    /** The searches the walks across the row's parameters go through
     *  ({@link CompositionBudget#SEARCHES_A_ROW_IS_COMPOSED_THROUGH}). */
    Tries searches() {
        return searches;
    }

    /** The assignments of the numbers the conditions on the way name that a row is composed for
     *  ({@link CompositionBudget#ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR}). */
    Tries composedOnTheWay() {
        return composedOnTheWay;
    }
}
