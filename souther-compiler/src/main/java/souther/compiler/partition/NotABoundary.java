package souther.compiler.partition;

/**
 * Why a comparison of a body bears no line.
 *
 * <p>An answer and never an absence. What these are told apart for is that a reader has to do
 * opposite things about them: one says the behavior draws no boundary here and a report saying
 * nothing is right, and the other two say it may well draw one that this could not be shown a row
 * against. Folded into one {@code false}, the second and third arrive downstream as the same silence
 * as the first — and whoever widens the measurement later has to work out again why anything was
 * left out.
 *
 * <p>One is said where more than one holds, and it is the one about the model. A reader told that a
 * comparison's outcome cannot be attributed to a row would go looking for a way to attribute it,
 * when the behavior's answer does not turn on the comparison at all.
 */
public enum NotABoundary {

    /**
     * Nothing reads the comparison's truth, so the behavior's answer does not turn on it.
     *
     * <p>The one of these that is about the model rather than about what can be measured. A body
     * binding {@code t.value < 240} to a name it never reads answers alike either side of 240, so a
     * partition there would have a report say this behavior distinguishes two ranges of its input
     * that it in fact answers the same — a distinction the model does not draw, asked for as rows.
     *
     * <p>Which values reach an answer is settled by {@link LiveFlow}, which over-reports on purpose:
     * a chain of dead bindings is still counted as read. So a comparison named this is one nothing
     * reads under any reading, and one not named this may still be one a sharper reading would.
     */
    NOTHING_READS_IT,

    /**
     * No run through the comparison can be recorded, so no row could be shown to have reached it.
     *
     * <p>What the plan numbering already answers. A comparison behind something that aborts, or in an
     * arm a condition never comes out the way of, is one no run gets to — and meeting a line takes
     * getting the comparison to answer, so a border there would owe a row nothing can measure.
     */
    NOTHING_RECORDS_IT,

    /**
     * One run passes the comparison more than once, so an outcome recorded at it belongs to no one
     * row.
     *
     * <p>A boundary the behavior may well draw. What stops it is the shape of the recording rather
     * than anything about the model: a recording holds that a place was passed and not how many
     * times, so a comparison inside a function value a combinator applies per element leaves two
     * outcomes in one run that cannot be told from two rows' outcomes. {@code Plan.mayRepeat} is
     * what says so.
     *
     * <p>Kept apart from the others for the day the measurement grows. A reading that could attribute
     * an outcome to the element it came from would make these lines, and nothing else about the
     * policy would have to change.
     */
    REPEATED_IN_ONE_RUN
}
