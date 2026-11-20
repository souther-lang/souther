package souther.compiler.inputs;

/**
 * Why neither that a run on the way to a rule stops at a construction, nor that none does, is
 * shown.
 *
 * <p>Each names what a proof that one does was not able to rest on: a proof needs a value of the
 * input that exists, takes the way to the rule and the way to the construction, has nothing before
 * the construction end the run, and does not meet what the construction asks, each shown whole.
 * Which of them is missing is what a reader extends to resolve it.
 */
public enum WhyAConstructionStopIsNotShown {
    /** That a run on the way to the rule gets to it is not shown: which runs do is not read, as
     *  of one worked out inside a function value, or met by the walk on more than one way. */
    REACH_NOT_SHOWN,
    /** What its type asks of the numbers it is made of is not read. */
    ASKS_NOT_READ,
    /** Something worked out before it may end the run first. */
    SOMETHING_BEFORE_IT_MAY_STOP,
    /** A condition on the way to the rule or to it is not a relation of whole numbers of the
     *  input, nor settled. */
    A_CONDITION_NOT_READ,
    /** What it asks, or what something worked out before it asks, is over something that is no
     *  number a row of the input holds at a place. */
    NOT_OVER_THE_INPUT,
    /** No value of the input is shown to exist holding the numbers asked. */
    NO_VALUE_SHOWN,
    /** No value tried takes the way and is refused by it, every value there was to try tried. */
    NO_VALUE_FOUND,
    /** No value tried is, and as many were tried as a search for an assignment on the way tries
     *  of one position, with more left. */
    NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED
}
