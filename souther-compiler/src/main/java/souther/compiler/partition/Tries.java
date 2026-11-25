package souther.compiler.partition;

/**
 * A figure of units a search spends one at a time, and whether the search was cut short by it.
 *
 * <p>Cut short is where a unit was wanted and there was none, or where the search says it left
 * something undone for want of one — and not where the last unit was spent and the search was
 * done. That a search used all it was given says nothing of whether it left anything, and a
 * report that it looked "within what is tried" is a report that something was left.
 *
 * <p>What a unit is, and so what the figure bounds, is each search's: a value tried, a way asked,
 * an element moved. A search spends one for every piece of work it does that the figure is to
 * bound, and a walk that could do work without spending — choosing through a list with nothing
 * at its end, say — is not bounded by it.
 */
final class Tries {

    private int left;

    /** How many times work was left undone for want of a unit, so that a holder shared by several
     *  searches can say which of them was cut short: one that saw this rise. */
    private int refusals;

    /** Of {@code figure} units. */
    Tries(int figure) {
        this.left = figure;
    }

    /** Whether a unit is spent: one is, where there is one, and where there is none that is asked
     *  for and refused, which cuts the search short. */
    boolean spend() {
        if (left <= 0) {
            refusals++;
            return false;
        }
        left--;
        return true;
    }

    /**
     * Whether there is a unit for one more piece of work, asked where that work is in front of
     * the search and before it is done or made: where there is none, it is left undone, which cuts
     * the search short. Nothing is spent; the work spends when it is done.
     *
     * <p>Asked by whatever produces work for the search as well as by what does it. Work produced
     * for a search with nothing left to spend is work no figure bounds.
     */
    boolean left() {
        if (left > 0) {
            return true;
        }
        refusals++;
        return false;
    }

    /** Whether none is left. */
    boolean spent() {
        return left <= 0;
    }

    /** That something was left undone for want of a unit. */
    void leftSomethingUndone() {
        refusals++;
    }

    /** Whether the search was cut short: a unit was wanted and there was none, or something was
     *  said to be left undone. */
    boolean cutShort() {
        return refusals > 0;
    }

    /** How many times work was left undone for want of a unit so far. */
    int refusals() {
        return refusals;
    }
}
