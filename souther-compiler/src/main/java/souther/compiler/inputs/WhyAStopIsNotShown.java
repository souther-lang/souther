package souther.compiler.inputs;

/**
 * Why neither that a run stops in what a rule works out, nor that none does, is shown.
 *
 * <p>Each names what a proof that one does was not able to rest on: a proof needs a value of the
 * input that exists, is on the way to the operation, has nothing before it end the run, and works
 * the operation out past its ends, each shown whole.
 *
 * <p>Each says what is said with it, so that whatever holds one, and whatever writes it, holds to
 * the same: whether it is of an operation ({@link #isOfAnOperation}), and whether where the stops
 * left untold are may be said beside it ({@link #restsOnStopsLeftUntold}).
 */
public enum WhyAStopIsNotShown {
    /** A run may stop in something worked out that is no operation told. */
    NO_OPERATION_TOLD(false, true),
    /** Something worked out before the step may end a run. */
    SOMETHING_BEFORE_IT_MAY_STOP(true, false),
    /** Some way a run gets to the step is not read, and no way read shows a run stopping there:
     *  of the step as a whole, and of no one operation of it. */
    REACH_NOT_SHOWN(false, false),
    /** A condition on the way is not a relation of whole numbers of the input, nor settled. */
    A_CONDITION_NOT_READ(true, false),
    /** It, or another operation that may be worked out first, is over something that is no
     *  number a row of the input holds at a place. */
    NOT_OVER_THE_INPUT(true, false),
    /** No value of the input is shown to exist holding the numbers asked. */
    NO_VALUE_SHOWN(true, false),
    /** No value tried is on the way and takes it past its ends, every value there was to try
     *  tried. */
    NO_VALUE_FOUND(true, false),
    /** No value tried is, and as many were tried as a search for an assignment on the way tries
     *  of one position, with more left. */
    NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED(true, false);

    private final boolean ofAnOperation;
    private final boolean restsOnStopsLeftUntold;

    WhyAStopIsNotShown(boolean ofAnOperation, boolean restsOnStopsLeftUntold) {
        this.ofAnOperation = ofAnOperation;
        this.restsOnStopsLeftUntold = restsOnStopsLeftUntold;
    }

    /** Whether it is said of an operation the rule works out, which it names; otherwise of a
     *  stop no operation names. */
    public boolean isOfAnOperation() {
        return ofAnOperation;
    }

    /** Whether it may rest on stops a reading left untold, whose places are then said with it. */
    public boolean restsOnStopsLeftUntold() {
        return restsOnStopsLeftUntold;
    }
}
