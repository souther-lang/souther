package souther.compiler.numeric;

import souther.compiler.types.TypeSymbol;

/**
 * What one is, on an order that counts.
 *
 * <p>A count is a number and says nothing on its own: 1 is a day, a second, a number and a case's
 * place depending on what is being counted. Which of those it is belongs to the order the count was
 * read off, and this is that order's answer to it.
 *
 * <p><b>What it is for is addition.</b> Two counts compare on one order and nothing brings two
 * orders' places together — that is {@link Place}'s rule and it stands. A form is where counts are
 * added rather than compared, and the question there is not whether the positions are written back
 * the same way but whether their counts mean the same thing. A decimal and an {@code Int} are
 * written back differently and both count in the number itself, so their difference is a number; a
 * date counts days, so a date and a number have no sum however well both sides type-checked.
 *
 * <p>Read off the order and not written beside it. Whether a form's positions can be added is then
 * one question with one answer, rather than a rule each reader of a form arrives at for itself —
 * and the rule that used to stand in for it, that every position of a form is on one order, refused
 * every form whose positions were written back differently whether or not they counted the same.
 */
public sealed interface CountingUnit {

    /** The number itself, which is what a whole number and a decimal both count in. */
    record ANumber() implements CountingUnit {}

    /** Days, standing for dates. */
    record Days() implements CountingUnit {}

    /** Seconds from the epoch, standing for date-times. Apart from {@link SecondsOfADay}: both are
     *  seconds and they are counted from different places, so their difference is not a duration. */
    record Seconds() implements CountingUnit {}

    /** Seconds from the start of a day, standing for times of day. */
    record SecondsOfADay() implements CountingUnit {}

    /** Nanoseconds from the epoch, standing for moments. */
    record Nanoseconds() implements CountingUnit {}

    /**
     * The places in one enumeration's declaration.
     *
     * <p>Named by the enumeration, because two enumerations place their cases independently: one is
     * not the same one in both, so two ordinals are one unit only where they order by the same sum.
     */
    record PlacesIn(TypeSymbol enumeration) implements CountingUnit {}

    /** An order with no count under it, whose values are therefore added to nothing. */
    record NotCounted() implements CountingUnit {}

    CountingUnit A_NUMBER = new ANumber();
    CountingUnit DAYS = new Days();
    CountingUnit SECONDS = new Seconds();
    CountingUnit SECONDS_OF_A_DAY = new SecondsOfADay();
    CountingUnit NANOSECONDS = new Nanoseconds();
    CountingUnit NOT_COUNTED = new NotCounted();

    /** Whether counts in this unit add up to anything. */
    default boolean counts() {
        return !(this instanceof NotCounted);
    }
}
