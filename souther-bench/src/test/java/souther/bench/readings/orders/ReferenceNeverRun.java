package souther.bench.readings.orders;

import java.util.Set;
import java.util.function.Function;

/**
 * A reference to the method that makes a copy, made and never run.
 *
 * <p>Making the reference copies nothing: a set is copied where something calls the function, and
 * nothing here does. It is a place the reading may begin and no copy for it to follow, so it makes
 * no copy for the reading to lose either.
 */
public final class ReferenceNeverRun {

    private ReferenceNeverRun() {}

    public static Function<Set<String>, Set<String>> theCopier() {
        return Set::copyOf;
    }
}
