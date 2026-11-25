package souther.compiler.partition;

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
 * <p>Which looking a row is is the caller's to say, and nothing here works it out. A caller that
 * makes one of these for each attempt has the figures of an attempt, which is what they were
 * before this held them.
 */
public final class LookingForARow {

    private final Tries searches;
    private final Tries rowsHanded =
            new Tries(CompositionBudget.ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW.maximum());
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

    /** The rows a walk hands a preference the choice among
     *  ({@link CompositionBudget#ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW}). */
    Tries rowsHanded() {
        return rowsHanded;
    }

    /** The assignments of the numbers the conditions on the way name that a row is composed for
     *  ({@link CompositionBudget#ASSIGNMENTS_ON_THE_WAY_COMPOSED_FOR}). */
    Tries composedOnTheWay() {
        return composedOnTheWay;
    }
}
