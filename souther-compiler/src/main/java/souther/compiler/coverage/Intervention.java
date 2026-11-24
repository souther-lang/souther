package souther.compiler.coverage;

/**
 * Which arm, if any, a run is asked to take in another arm's place, and which walk, if any, it is
 * asked to run rewritten.
 *
 * <p>Beside {@link Probe} and not part of it. A probe says what a run did; this says which program
 * the run is of. Classes that record a run carry, at an arm with siblings, a switch that asks this
 * which expression to answer with — the arm's own, unless the run on this thread asked for one of its
 * siblings ({@link ArmReplacements}) — and at a walk, a switch that asks this how to walk
 * ({@link WalkRewrites}). A run asks by naming the sites to rewrite and what to answer with at each
 * ({@link Rewriting}).
 *
 * <p>Per thread, because a run is per thread, and let go of on every way out for the reason the
 * recording is: a worker outlives the row it ran.
 *
 * <p>A run that asks for a rewrite is not one anything is recording. What it goes through is a
 * program the author did not write, and its places are not the module's.
 */
public final class Intervention {

    /** What this thread's runs asked for. Null where the run is of the program as written, which
     *  is every run but the ones that asked. */
    private static final ThreadLocal<Rewriting> ASKED = new ThreadLocal<>();

    /**
     * Called by the classes at an arm with siblings: the part to answer with at {@code site}, or
     * {@code -1} for the arm's own. Public and static because that is what an
     * {@code invokestatic} from a generated class needs.
     */
    public static int replacementAt(int site) {
        Rewriting asked = ASKED.get();
        if (asked == null) {
            return -1;
        }
        Integer with = asked.arms().get(site);
        return with == null ? -1 : with;
    }

    /**
     * Called by the classes as a walk is entered: the {@link WalkRewrite#code} of the rewrite to
     * run the walk at {@code site} as, or {@code -1} for the walk as written. Public and static for
     * the reason {@link #replacementAt} is.
     */
    public static int walkAt(int site) {
        Rewriting asked = ASKED.get();
        if (asked == null) {
            return -1;
        }
        WalkRewrite how = asked.walks().get(site);
        return how == null ? -1 : how.code();
    }

    /** Asks the runs on this thread to answer as {@code asked} says at its sites. */
    public static void begin(Rewriting asked) {
        ASKED.set(asked);
    }

    /** Lets go of what was asked, so the next run on this thread is of the program as written. */
    public static void end() {
        ASKED.remove();
    }

    private Intervention() {}
}
