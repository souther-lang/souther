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
 * <p>The set is per thread because a row is per thread. Rows are evaluated on their own workers, and a
 * thread-shared set would attribute every row's arms to every row.
 */
public final class Probe {

    /** What the thread running a row has been through. Null between rows: a hit with nothing collecting
     * is a call from code nobody is measuring, and dropping it is right. */
    private static final ThreadLocal<BitSet> TAKEN = new ThreadLocal<>();

    /** Called by probed code. Public and static because that is what an {@code invokestatic} from a
     * generated class needs. */
    public static void hit(int site) {
        BitSet taken = TAKEN.get();
        if (taken != null) {
            taken.set(site);
        }
    }

    /** Starts collecting on this thread. */
    public static void begin() {
        TAKEN.set(new BitSet());
    }

    /** What this thread has been through so far, as a set nothing can go on changing. */
    public static Set<Integer> taken() {
        BitSet taken = TAKEN.get();
        if (taken == null) {
            return Set.of();
        }
        Set<Integer> sites = new LinkedHashSet<>();
        for (int at = taken.nextSetBit(0); at >= 0; at = taken.nextSetBit(at + 1)) {
            sites.add(at);
        }
        return Set.copyOf(sites);
    }

    /** Stops collecting, and lets go of the set. A worker thread outlives the row it ran, so a set
     * left behind would be the next row's starting point. */
    public static void end() {
        TAKEN.remove();
    }

    private Probe() {}
}
