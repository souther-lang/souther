package souther.compiler;

/**
 * Whether a report leaves a comparison unread for anything but a stop nothing tells: an operation
 * a run works out evaluating it that may pass its type, said apart from how the comparison is
 * read. A test about how a comparison is read asks this, and leaves whether a run stops in it to
 * the tests about that.
 */
public final class UnreadBesideItsStops {

    /** What the report says of a run that may stop where nothing says. */
    public static final String STOPS_NOT_ALL_TOLD =
            "an operation that may end the run where nothing here says";

    private UnreadBesideItsStops() {
    }

    /** Whether {@code report}, a report in English, leaves a comparison unread for anything but
     *  a stop nothing tells. */
    public static boolean in(String report) {
        return report.lines().anyMatch(line -> line.contains("not read")
                && !line.contains(STOPS_NOT_ALL_TOLD));
    }
}
