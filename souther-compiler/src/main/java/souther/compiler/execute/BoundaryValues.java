package souther.compiler.execute;

import souther.compiler.ast.Hir;
import souther.compiler.check.BoundaryInput;
import souther.compiler.observe.ObservedValue;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Whether a value composed elsewhere can be built at a module's boundary.
 *
 * <p>The question a generator cannot answer for itself. Which values a type admits together is the
 * derived decoder's business — an invariant relating two fields refuses a pair that each field would
 * have accepted alone — so the only way to know is to put the value through the decoder that a row's
 * own fixture goes through, which means running what the compile produced.
 *
 * <p>A way to ask rather than an answer, because a search asks it of one candidate after another and
 * what it is asking against does not change between them.
 *
 * <p>So one of these is a question about a fixed world, and the same value asked about twice is
 * answered the same way twice. What it is asked against — the module, the classes the compile
 * produced, the loader that holds them — is the instance itself, so the position and the fixture are
 * the whole of what decides an answer and an answer once given may be kept ({@link #remembering}).
 * An implementation whose answer moved with something else — a count of the candidates it has seen,
 * a point a search happens to be at — would be answering another question.
 */
@FunctionalInterface
public interface BoundaryValues {

    /**
     * What building the value at a position came to: what was built, or why nothing was.
     *
     * <p>Both, because the one thing that builds a value is the only thing that can say what it came
     * to be. Answered as whether it was refused, a caller that wanted to know where the value landed
     * had to work it out from what it had asked for — and what it asked for is a reading, while what
     * was built went through the decoders and the invariants and is what a row would carry.
     *
     * <p>Throws {@link LinkageError} where the runtime is absent, which is not a fact about the
     * value.
     */
    Built build(BoundaryInput at, Hir.Expr fixture);

    /**
     * The same answers, each worked out once.
     *
     * <p>A search asks about one candidate at every point of a border it is tried at and under every
     * way of standing the dependencies in, and the decoder says the same thing each time. Whether
     * the value stands at the point is the other half of that question and is asked of what comes
     * back here, every time; it is not this one's to keep.
     *
     * <p>What is kept is what came back: a value, or a refusal, both of which are what the decoder
     * says about the fixture. What was thrown is not kept. A runtime that would not link and an
     * evaluation that ran out of what it may spend are about this compile and this run, and the next
     * asking is entitled to find out again.
     *
     * <p>Kept for as long as {@code source} is, because {@code source} is what the answers are
     * about. Shared between two of them, an answer worked out against one module's classes would be
     * handed back about the other's.
     */
    static BoundaryValues remembering(BoundaryValues source) {
        record Asked(BoundaryInput at, Hir.Expr fixture) {}
        Map<Asked, Built> answered = new ConcurrentHashMap<>();
        return (at, fixture) -> {
            Asked asked = new Asked(at, fixture);
            Built had = answered.get(asked);
            if (had != null) {
                return had;
            }
            // Built outside the map rather than inside computeIfAbsent: a decoder can run for a while,
            // and the map would hold everything hashed beside this fixture until it finished. Two
            // threads that race build the same answer, and the first one kept is the one both return.
            Built made = source.build(at, fixture);
            Built kept = answered.putIfAbsent(asked, made);
            return kept == null ? made : kept;
        };
    }

    /** What came of building one value. */
    sealed interface Built {

        /** It built, and this is what it came to. */
        record Value(ObservedValue observed) implements Built {}

        /** It did not, and why. Never a claim that no value of the shape can be built. */
        record Refused(String why) implements Built {}
    }
}
