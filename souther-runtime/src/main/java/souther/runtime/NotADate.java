package souther.runtime;

/**
 * The failure case of {@code Date.fromParts}: the three Ints name no day. February the 30th, month
 * 13, a year outside what a date can hold. A built-in data with no fields; the only value is
 * {@link #INSTANCE}, mirroring {@link NotANumber}.
 *
 * <p>One case for both a calendar that has no such day and a year a date cannot reach, as
 * {@code NotANumber} is one case for text that is no number and for a number too large to hold. What
 * a caller does with either is the same: the parts it had do not name a date.
 */
public final class NotADate {

    public static final NotADate INSTANCE = new NotADate();

    public NotADate() {}
}
