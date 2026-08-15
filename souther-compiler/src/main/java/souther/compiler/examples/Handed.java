package souther.compiler.examples;

import java.util.function.Supplier;

/**
 * One value a row hands whatever applies the behavior for it.
 *
 * <p>Two faces of one value, because the two ends of an application are not always in one loader.
 * {@link #built} is the value as this compile built it — an instance of a class the run's loader
 * defined, which is what an answerer applying this compile's own classes takes. {@link #neutral} is
 * the same value in the form a derived decoder reads, which is what an answerer whose classes are not
 * this compile's puts through its own decoders.
 *
 * <p>Reading a value back is already loader-free and stays where it is: what a run answered with is
 * read by name and by the accessor every data has, so the answer needs no second face. Only the
 * direction that hands a value over is checked for class identity — a typed {@code apply} and an
 * injecting constructor both are — so only that direction is written here. The asymmetry is the
 * asymmetry of the JVM, and stating it is better than making both ends carry a crossing one of them
 * does not need.
 *
 * <p>{@link #neutral} is worked out on the first call and not before. An answerer applying this
 * compile's own classes never asks for it and never pays for the walk.
 *
 * <p>Made here, never by a caller. The two faces are one value, and that they are is established by
 * the walk that produced the second from the first. An implementation supplied from outside could
 * hand over a pair that is not one value, and nothing downstream could tell.
 */
public final class Handed {

    private final Object built;
    private final Supplier<NeutralValue> neutralise;
    private NeutralValue neutral;

    Handed(Object built, Supplier<NeutralValue> neutralise) {
        this.built = built;
        this.neutralise = neutralise;
    }

    /** The value as this compile built it. */
    public Object built() {
        return built;
    }

    /**
     * The same value in the form a derived decoder reads.
     *
     * <p>Throws where the value cannot be read back into that form, which is a fact about this
     * compile's value and not about whatever is applying the behavior. An answerer must let what this
     * throws out as it stands: read as the applied code having failed, a run would report a model that
     * may be right as one that aborted. What it throws is not a type this package publishes, so an
     * answerer cannot catch it by name and has no reason to catch it at all — everything it did not
     * raise itself goes out.
     *
     * <p>What a row makes of one is not settled here, because no answerer a compile has crosses: the
     * one it has of its own applies the classes these values already are. It is settled by whatever
     * first supplies an answerer that does, which is also what decides whether such a row is a
     * failure or a row that could not be decided.
     */
    public NeutralValue neutral() {
        if (neutral == null) {
            neutral = neutralise.get();
        }
        return neutral;
    }
}
