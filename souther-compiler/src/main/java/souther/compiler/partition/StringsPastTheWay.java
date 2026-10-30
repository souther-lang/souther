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

    /**
     * Whether the way allows no count at all. A statement about the numbers and nothing about the
     * strings: whether a string holds an allowed count is {@link #strings}, and a class counting
     * no code point allows counts that no string holds. Which strings of a place are of these is
     * met with what the place admits, where the classes are made.
     */
    boolean isEmpty();

    /**
     * The strings holding an allowed count, or null where no count is allowed or the counts are
     * past what a pattern counts.
     */
    PatternPlan strings();

    /**
     * The strings holding a count that is not allowed, or null where every count is allowed, none
     * is, or the counts are past what a pattern counts.
     */
    PatternPlan stringsOutside();
}
