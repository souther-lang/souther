package souther.compiler.inputs;

/**
 * Why neither that a run stops in what a rule works out, nor that none does, is shown.
 *
 * <p>Each names what a proof that one does was not able to rest on: a proof needs a value of the
 * input that exists, is on the way to the operation, has nothing before it end the run, and works
 * the operation out past its ends, each shown whole.
 */
public enum WhyAStopIsNotShown {
    /** A run may stop in something worked out that is no operation told. */
    NO_OPERATION_TOLD,
    /** A run may stop on rows the statement says of its own, which are no operation of numbers. */
    ON_ROWS_OF_THE_STATEMENT,
    /** It is worked out on an arm of a choice. */
    ON_AN_ARM,
    /** It is worked out on each application of a closure. */
    ON_AN_APPLICATION,
    /** Some operation the rule works out is not told, or not on every run. */
    NOT_EVERY_OPERATION_TOLD,
    /** Something worked out before the rule may end a run. */
    SOMETHING_BEFORE_IT_MAY_STOP,
    /** A condition on the way is not a relation of whole numbers of the input, nor settled. */
    A_CONDITION_NOT_READ,
    /** It, or another operation that may be worked out first, is over something that is no
     *  number a row of the input holds at a place. */
    NOT_OVER_THE_INPUT,
    /** No value of the input is shown to exist holding the numbers asked. */
    NO_VALUE_SHOWN,
    /** No value tried is on the way and takes it past its ends, every value there was to try
     *  tried. */
    NO_VALUE_FOUND,
    /** No value tried is, and as many were tried as a search for an assignment on the way tries
     *  of one position, with more left. */
    NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED
}
