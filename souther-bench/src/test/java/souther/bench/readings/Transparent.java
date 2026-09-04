package souther.bench.readings;

/**
 * An owner of a question that is walked through all the same.
 *
 * <p>It reads raw structure to answer, like the authority beside it. What it does not do is finish
 * on its own: a caller reaches through it, so a boundary here would put whatever the caller wrote
 * on the far side of the check. Written with the reading inside for the fixture's sake — what makes
 * a place transparent is that a caller's code is reached from it, and the walk cannot see which
 * side wrote what.
 */
public final class Transparent {

    private Transparent() {}

    /** What the name comes to, read on the way. */
    public static boolean answering(Written.Names names, String name) {
        return Helpers.isARecord(names, name);
    }
}
