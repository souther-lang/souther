package souther.compiler.check;

import java.util.List;

/**
 * What the declarations hold the date at one place to, where that is shown to be the whole of
 * what they say of it, or that it is not.
 *
 * <p>Two answers and not a list beside a flag. An empty list of rules is said of a date the rules
 * say nothing beyond the class of, and of a date they say something of that nothing here read;
 * only the first is a date whose every day of the class is a value. A reader proving a date exists
 * reads {@link Whole} alone, and {@link NotWhole} is no claim that none does.
 */
public sealed interface DateRules {

    /**
     * Everything the declarations say of the date: the days from {@code least} to {@code most},
     * both counted, the class {@code held} of its parts, and the rules {@code parts} hold two of
     * them to. A date of all of them is a value the declarations leave the place, and where
     * {@code least} is past {@code most} the declarations leave it no day.
     */
    record Whole(long least, long most, HeldClass held, List<RuleOfDateParts> parts)
            implements DateRules {

        public Whole {
            parts = List.copyOf(parts);
        }
    }

    /** Some rule reaching the date is one these do not hold: unread, a choice, a move, or a
     *  relation to another place. */
    record NotWhole() implements DateRules {}

    DateRules NOT_WHOLE = new NotWhole();

    /** What no declaration says anything of: every date the calendar has. */
    DateRules EVERY_DATE = new Whole(DatePartsLeft.FIRST_DAY, DatePartsLeft.LAST_DAY,
            HeldClass.NONE, List.of());
}
