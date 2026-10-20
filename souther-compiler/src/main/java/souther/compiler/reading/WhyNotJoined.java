package souther.compiler.reading;

/**
 * Why a sum of the elements a comparison keeps could not be joined to the evaluations of that
 * comparison, and so was not asked of the rows.
 *
 * <p>The sum is a meeting all the same: it is made of decisions, and nothing here says it is not.
 * What is missing is which evaluation a run records is which application's, and every reason below
 * is a way that was out of reach of this reading rather than a fact about what a sum means. A
 * measure that went without one of these says so ({@code Weakening.MeetingsNotJoined}), and does not
 * count the sum among the meetings nothing is owed at.
 */
public enum WhyNotJoined {

    /** An occurrence is kept by more than one truth, so which evaluation of a later one is its
     *  depends on how the earlier ones came out. The evaluation is determined once the first
     *  stage's outcomes are; this does not work it out. */
    KEPT_BY_SEVERAL,

    /** An occurrence is kept by what is not a truth about it, such as the arm of a choice. */
    KEPT_BY_ANOTHER_KIND,

    /** What keeps an occurrence is not a comparison this reading places: a truth read off a field,
     *  a conjunction, a call. It is a decision all the same, and no place of the tree that runs
     *  records which way it came out apart from the others. */
    NOT_ONE_COMPARISON,

    /** The comparison asks which case of a union a value is, which an arm of a choice records and
     *  a visit to a comparison does not. */
    A_COMPARISON_OF_CASES,

    /** The comparison is of a number no input position holds, so no row can be steered by it. */
    A_NUMBER_NO_INPUT_HOLDS,

    /** No run is recorded at the comparison: the plan numbered no place for it. */
    NO_RUN_IS_RECORDED_AT_IT,

    /** A decision is of an evaluation past those a recording keeps, which is a claim no
     *  observation could answer. */
    MORE_VISITS_THAN_ARE_RECORDED,

    /** The occurrences are not all kept by the one comparison, so they are not one closure applied
     *  to each. */
    NOT_ONE_CLOSURE,

    /** Two occurrences kept by one application disagree about it, which no one application
     *  does. */
    AN_APPLICATION_SAID_TWO_THINGS,

    /** The expansion of the call in the tree that runs does not hold the comparison once, so which
     *  evaluation is recorded where is not one answer. */
    NOT_ONE_COMPARISON_THAT_RUNS,

    /** The container holds more occurrences than the walk writes out. */
    MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT
}
