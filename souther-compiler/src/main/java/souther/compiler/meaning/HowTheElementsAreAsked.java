package souther.compiler.meaning;

/**
 * How an operation goes through the elements of a container, as far as it decides what the
 * operation answers where what it asks of one element answers nothing on some rows.
 *
 * <p>A statement about some element is what the operation answers where the statement answers on
 * every element: then which element a run reaches first changes nothing. Where it answers nothing
 * on one — a quotient by what the element holds divides by nought there — the run stops at that
 * element if it reaches it, and what the operation answers turns on whether it does.
 */
public enum HowTheElementsAreAsked {

    /**
     * Every element is asked, whatever the others answered: the operation answers where every
     * element does, and there it answers what the statement about some element says.
     */
    EVERY_ONE,

    /**
     * Each element is asked in turn until one meets the statement, in an order something else the
     * row is asked for may turn on.
     *
     * <p>Then what it answers is read only where whether an element answers is the same for every
     * element: a run stops at the first element it reaches where it stops at any, so it answers
     * where every element does, as {@link #EVERY_ONE} says.
     */
    UNTIL_ONE_MEETS_IT,

    /**
     * Each element is asked in turn until one meets the statement, in an order the row writes as
     * it likes and that nothing else the row is asked for turns on.
     *
     * <p>Then it is read as answering that some element meets it wherever one does, and that none
     * does where every element answers and none meets it. On a row whose run answers, that is what
     * the run answered: every element before the one it stopped at answered. The first also takes
     * in rows whose run stops at an element before the one meeting it, and so answers nothing;
     * each of them, with the element meeting it written first, is a row that does meet it, and is
     * the same row to everything else asked of it. So whether some row comes out meeting it, under
     * anything else asked, is answered as it is of the runs.
     */
    UNTIL_ONE_MEETS_IT_IN_AN_ORDER_OF_THE_ROWS,

    /**
     * Neither of those, or not known to be: which element a run stops at turns what the operation
     * answers, and nothing says which.
     */
    NOT_SAID
}
