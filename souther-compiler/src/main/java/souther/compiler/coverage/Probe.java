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
 * <p>One recording and not one per shape of thing recorded. What a run leaves behind is the arms it
 * passed through and the ways its comparisons came out, and the two are one run's — begun together,
 * read together and let go together. Kept as two thread locals they would be two lifecycles that
 * happen to be driven from the same three calls, and a shape added later would be a third: nothing
 * would stop one of them being begun and another read.
 *
 * <p>Which is not the same as writing them into one set. The two families take their numbers from
 * one counter because the call carries one number; what each call records is what that call was
 * for, and the recording says which rather than leaving a reader to ask the numbering afterwards.
 */
public final class Probe {

    /** What the thread running a row has been through. Null between rows: a hit with nothing
     * collecting is a call from code nobody is measuring, and dropping it is right. */
    private static final ThreadLocal<Recording> RECORDING = new ThreadLocal<>();

    /** What one thread is building up while a row runs. Mutable, unshared, and never handed out —
     * what a caller gets is {@link Observation}, which is a value. */
    private static final class Recording {

        /** What the classes this run is going through were numbered by. Taken where the collecting
         * starts, because that is where the classes about to be run are in hand — nothing inside
         * one has a numbering to say what its numbers address. */
        private final NumberingIdentity numbering;

        /** The arms, as bits, because an arm is a number and a run passes many. */
        private final BitSet arms = new BitSet();

        /** The comparisons, as the ways they came out. A comparison is recorded by how it answered
         *  and by nothing else: that a way out of it exists is its having been reached. */
        private final Set<ComparisonOutcome> comparisons = new LinkedHashSet<>();

        private Recording(NumberingIdentity numbering) {
            this.numbering = numbering;
        }
    }

    /** Called by probed code where an arm ran. Public and static because that is what an
     * {@code invokestatic} from a generated class needs. */
    public static void hit(int site) {
        Recording recording = RECORDING.get();
        if (recording != null) {
            recording.arms.set(site);
        }
    }

    /**
     * Called by probed code where a comparison this plan numbers answered, with the value it
     * answered.
     *
     * <p>One entry and not two. That the comparison was reached and the way it came out are one
     * fact recorded once: a way out of it exists, and a reader asking whether it was reached is
     * asking whether any does. Written as a way out and a bit beside it, the two would be a rule
     * something has to keep in step, and a run holding one without the other would be a value every
     * reader had to be told what to make of.
     *
     * <p>Takes the value rather than a second site chosen from it, so that the numbering the emitter
     * was given is the numbering it uses and a way out is never a number a reading picked.
     */
    public static void compared(boolean held, int site) {
        Recording recording = RECORDING.get();
        if (recording != null) {
            recording.comparisons.add(new ComparisonOutcome(site, held));
        }
    }

    /**
     * Starts collecting on this thread, of classes numbered by {@code numbering}.
     *
     * <p>Said here because here is where it can be. The numbers a probed class writes are the
     * numbering's, and the class has nothing to say about which numbering that was; what does is
     * whoever loaded the classes and is about to run a row through them.
     */
    public static void begin(NumberingIdentity numbering) {
        RECORDING.set(new Recording(numbering));
    }

    /**
     * What this thread has been through so far, as one value nothing can go on changing.
     *
     * <p>Refused where nothing is collecting. A snapshot has to say which numbering its numbers are
     * of, and there is none to say when no recording was begun — so what a caller has then is no
     * account of a run rather than a run that passed nowhere, and it is the caller that knows which:
     * it is the one that decided whether to begin.
     */
    public static Observation snapshot() {
        Recording recording = RECORDING.get();
        if (recording == null) {
            throw new IllegalStateException("nothing is recording on this thread, so there is no"
                    + " run to take a snapshot of; a row nobody watched has no account");
        }
        Set<Integer> arms = new LinkedHashSet<>();
        for (int at = recording.arms.nextSetBit(0); at >= 0;
                at = recording.arms.nextSetBit(at + 1)) {
            arms.add(at);
        }
        return new Observation(recording.numbering, arms, recording.comparisons);
    }

    /** Stops collecting, and lets go of the recording. A worker thread outlives the row it ran, so a
     * recording left behind would be the next row's starting point. */
    public static void end() {
        RECORDING.remove();
    }

    private Probe() {}
}
