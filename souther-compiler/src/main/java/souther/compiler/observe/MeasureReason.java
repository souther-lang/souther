package souther.compiler.observe;

/**
 * Why a measure has no number.
 *
 * <p>Which reasons a measure can have stays the measure's own business. What is not the measure's is
 * which kind of no-number a reason is, and that is now the reason's <em>type</em> rather than
 * something it answers: {@link souther.compiler.query.NotApplicableReason},
 * {@link souther.compiler.query.NotMeasuredReason} and {@link souther.compiler.query.FailureReason}
 * are three interfaces and a constant implements exactly one. Each of them names its arms, which it
 * can do only where they are written — so the three stand with the measures and this stands with
 * what reads a measure.
 *
 * <p>It used to answer {@code status()} and {@code somethingWasUnreadable()}, and a measure whose
 * status and reason disagreed was refused where the value was built. A check over a state the type
 * still lets anybody write is a check somebody has to keep running; three types is the same rule
 * with nothing left to run (issue #953).
 *
 * <p>{@code name()} is here so that a document can write the constant's word without every reader
 * holding the enum. It is what {@link Enum} already provides, which is why every reason is one.
 */
public interface MeasureReason {

    /** The constant's own word, which is what the JSON form lowercases. */
    String name();

    /**
     * What this reason is a fact about.
     *
     * <p>The reason's own answer, asked at its declaration. Three readers put this question and
     * none of them can work it out from what it holds: a surface decides from it whether a line of
     * its own is printed, a fold over the readings of one line decides from it whether the reasons
     * two readings gave are two facts or one fact said twice, and whoever adds a reason has to say
     * which it is. Answered at each of those instead, one fact about a constant is spelled in as
     * many tables as there are readers, and a constant added later reaches the ones whose author
     * remembered it.
     *
     * <p><b>Not read off anything else the reason answers, and nothing else read off this.</b>
     * Whether a row could be hiding behind a reason is a different question with a different
     * answer — a reading of the arms that came back unreadable is a fact about the behavior and may
     * be hiding a row — and a reader wanting that one asks the measure that has it.
     */
    About about();

    /** What a reason is a fact about, which is a property of the reason and of nothing around it. */
    enum About {

        /**
         * The run, and not the behavior the measure is of.
         *
         * <p>What a build asked for is an input to the whole run, so every measure of every
         * behavior says the same one — a surface printing a line per measure would say one fact as
         * many times as the module has behaviors, and readings of one line that say this say one
         * fact rather than several.
         */
        THE_RUN,

        /** The behavior the measure is of, so the measure says it and two behaviors can say
         *  different ones. */
        THE_BEHAVIOR
    }
}
