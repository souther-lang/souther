package souther.compiler.partition;

import souther.compiler.regex.PatternPlan;

/**
 * The strings a run can have where it gets past everything its way states, when what the way
 * ties to other numbers is one count of the string: how many code points it holds
 * ({@link LengthsPastTheWay.Lengths}), or how many of them are in a class
 * ({@link CodePointsPastTheWay}).
 *
 * <p>The two counts are different numbers of one string, and a statement of the way is about one
 * of them. What a statement of one says of the other is not worked out, so a way that states both
 * is not read.
 */
sealed interface StringsPastTheWay
        permits LengthsPastTheWay.Lengths, CodePointsPastTheWay {

    /** Whether no string is of these. */
    boolean isEmpty();

    /**
     * The strings of these, or null where there are none or the counts are past what a pattern
     * counts.
     */
    PatternPlan strings();

    /**
     * The strings that are not of these, or null where there are none of them or the counts are
     * past what a pattern counts.
     */
    PatternPlan stringsOutside();
}
