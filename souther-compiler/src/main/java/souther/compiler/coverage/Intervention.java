package souther.compiler.coverage;

import java.util.Map;

/**
 * Which arm, if any, a run is asked to take in another arm's place.
 *
 * <p>Beside {@link Probe} and not part of it. A probe says what a run did; this says which program
 * the run is of. Classes that record a run carry, at an arm with siblings, a switch that asks this
 * which expression to answer with — the arm's own, unless the run on this thread asked for one of its
 * siblings ({@link ArmReplacements}). A run asks by naming the sites of the arm to replace and the
 * part to answer with at each.
 *
 * <p>Per thread, because a run is per thread, and let go of on every way out for the reason the
 * recording is: a worker outlives the row it ran.
 *
 * <p>A run that asks for a replacement is not one anything is recording. What it goes through is a
 * program the author did not write, and its places are not the module's.
 */
public final class Intervention {

    /** The sites to replace and the part to answer with at each. Null where the run is of the
     *  program as written, which is every run but the ones that asked. */
    private static final ThreadLocal<Map<Integer, Integer>> REPLACING = new ThreadLocal<>();

    /**
     * Called by the classes at an arm with siblings: the part to answer with at {@code site}, or
     * {@code -1} for the arm's own. Public and static because that is what an {@code invokestatic}
     * from a generated class needs.
     */
    public static int replacementAt(int site) {
        Map<Integer, Integer> replacing = REPLACING.get();
        if (replacing == null) {
            return -1;
        }
        Integer with = replacing.get(site);
        return with == null ? -1 : with;
    }

    /** Asks the runs on this thread to answer with {@code replacing}'s parts at its sites. */
    public static void begin(Map<Integer, Integer> replacing) {
        REPLACING.set(Map.copyOf(replacing));
    }

    /** Lets go of what was asked, so the next run on this thread is of the program as written. */
    public static void end() {
        REPLACING.remove();
    }

    private Intervention() {}
}
