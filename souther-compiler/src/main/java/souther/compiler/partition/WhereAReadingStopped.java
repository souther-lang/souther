package souther.compiler.partition;

/**
 * Where the arithmetic's reading of a comparison stopped, as the reader that stopped saw it.
 *
 * <p>Decided where the reading stopped, from the expression it stopped at and why, and carried
 * from there with the reasons it left. Asked afterwards of the comparison's sides and of the words
 * the reasons came to, it was a second account of the stop: a side scanned for a call found the
 * call whichever part the reading stopped at, and a word told apart from other words held only as
 * long as no other stop came to the same one.
 */
enum WhereAReadingStopped {

    /**
     * Inside a number a call into a behavior's body or a walk from a seed works out of the input,
     * which the reading has no rule for and a run works out all the same. What a run worked out
     * there is what places a row ({@link ComparisonAssessment#onItsRuns}).
     */
    IN_WHAT_A_RUN_WORKS_OUT,

    /**
     * Anywhere else: at arithmetic no form says, at a figure of this compiler's work, at a value
     * that is no number a run of this behavior works out, or where no single reading stopped at
     * all. What stopped it is said as that.
     */
    ELSEWHERE;

    /** Where readings that each stopped stopped, taken as one: in what a run works out only where
     *  every one of them did. */
    WhereAReadingStopped and(WhereAReadingStopped other) {
        return this == IN_WHAT_A_RUN_WORKS_OUT && other == IN_WHAT_A_RUN_WORKS_OUT
                ? IN_WHAT_A_RUN_WORKS_OUT : ELSEWHERE;
    }
}
