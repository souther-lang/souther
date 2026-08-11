package souther.runtime;

/**
 * The failure case of {@code Time.fromParts}: the three Ints name no time of day. Hour 24, minute
 * 60, the leap second. A built-in data with no fields; the only value is {@link #INSTANCE},
 * mirroring {@link NotADate}.
 */
public final class NotATime {

    public static final NotATime INSTANCE = new NotATime();

    public NotATime() {}
}
