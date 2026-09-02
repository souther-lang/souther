package souther.compiler.coverage;

import java.util.BitSet;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Where a run went, recorded by the code as it goes.
 *
 * <p>This class is the compiler's, not the runtime's, and that is the whole point of putting it here.
 * A probed class calls {@code souther.compiler.coverage.Probe.hit}, and the loader that runs one
 * delegates every name it does not itself hold to its parent, whose chain ends at the compiler's own
 * loader — so the call resolves while measuring and there is nothing to resolve anywhere else. Shipped
 * classes are generated without the calls, so a jar never refers to this and a project that depends on
 * the runtime never sees it.
 *
 * <p>The recording is per thread because a row is per thread. Rows are evaluated on their own workers,
 * and a thread-shared recording would attribute every row's arms to every row.
 *
 * <p>One recording and not one per shape of thing recorded. What a run leaves behind is the places it
 * passed through and the ways its comparisons came out, and the two are one run's — begun together,
 * read together and let go together. Kept as two thread locals they would be two lifecycles that
 * happen to be driven from the same three calls, and a shape added later would be a third: nothing
 * would stop one of them being begun and another read.
 */
public final class Probe {

    /** What the thread running a row has been through. Null between rows: a hit with nothing
     * collecting is a call from code nobody is measuring, and dropping it is right. */
    private static final ThreadLocal<Recording> RECORDING = new ThreadLocal<>();

    /** What one thread is building up while a row runs. Mutable, unshared, and never handed out —
     * what a caller gets is {@link Observation}, which is a value. */
    private static final class Recording {

        private final BitSet taken = new BitSet();
        private final Set<ComparisonOutcome> comparisons = new LinkedHashSet<>();
    }

    /** Called by probed code where an arm ran. Public and static because that is what an
     * {@code invokestatic} from a generated class needs. */
    public static void hit(int site) {
        Recording recording = RECORDING.get();
        if (recording != null) {
            recording.taken.set(site);
        }
    }

    /**
     * Called by probed code where a comparison this plan numbers answered, with the value it
     * answered.
     *
     * <p>Records both facts, because they are one event. That the comparison was reached and the way
     * it came out are read by different measures, and emitting a call each would make "a way recorded
     * implies its comparison reached" a rule the emitter has to keep rather than something no run can
     * be found breaking.
     *
     * <p>Takes the value rather than a second site chosen from it, so that the numbering the emitter
     * was given is the numbering it uses and a way out is never a number a reading picked.
     */
    public static void compared(boolean held, int site) {
        Recording recording = RECORDING.get();
        if (recording != null) {
            recording.taken.set(site);
            recording.comparisons.add(
                    new ComparisonOutcome(new ComparisonEmissionSite(site), held));
        }
    }

    /** Starts collecting on this thread. */
    public static void begin() {
        RECORDING.set(new Recording());
    }

    /** What this thread has been through so far, as one value nothing can go on changing. */
    public static Observation snapshot() {
        Recording recording = RECORDING.get();
        if (recording == null) {
            return Observation.NONE;
        }
        Set<Integer> sites = new LinkedHashSet<>();
        for (int at = recording.taken.nextSetBit(0); at >= 0;
                at = recording.taken.nextSetBit(at + 1)) {
            sites.add(at);
        }
        return new Observation(sites, recording.comparisons);
    }

    /** Stops collecting, and lets go of the recording. A worker thread outlives the row it ran, so a
     * recording left behind would be the next row's starting point. */
    public static void end() {
        RECORDING.remove();
    }

    private Probe() {}
}
