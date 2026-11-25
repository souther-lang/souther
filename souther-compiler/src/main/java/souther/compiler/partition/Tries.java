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
    private boolean refused;

    /** Of {@code figure} units. */
    Tries(int figure) {
        this.left = figure;
    }

    /** Whether a unit is spent: one is, where there is one, and where there is none that is asked
     *  for and refused, which cuts the search short. */
    boolean spend() {
        if (left <= 0) {
            refused = true;
            return false;
        }
        left--;
        return true;
    }

    /** Whether none is left. */
    boolean spent() {
        return left <= 0;
    }

    /** That something was left undone for want of a unit. */
    void leftSomethingUndone() {
        refused = true;
    }

    /** Whether the search was cut short: a unit was wanted and there was none, or something was
     *  said to be left undone. */
    boolean cutShort() {
        return refused;
    }
}
