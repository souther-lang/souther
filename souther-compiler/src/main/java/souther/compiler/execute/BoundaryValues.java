package souther.compiler.execute;

import souther.compiler.ast.Hir;
import souther.compiler.check.BoundaryInput;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

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
 * the whole of what decides an answer and an answer once given may be kept by whoever asked for it.
 * An implementation whose answer moved with something else — a count of the candidates it has seen,
 * a point a search happens to be at — would be answering another question.
 */
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
     * What the decoder of {@code type} says of the value on its own, not put inside anything.
     *
     * <p>The same decoder a value of that type goes through wherever it stands, so a value it refuses
     * here is refused inside every value that holds one. What it admits here says nothing about
     * those: a rule relating two fields refuses a pair whose halves each built.
     *
     * <p>Throws {@link LinkageError} where the runtime is absent, as {@link #build} does.
     */
    OnItsOwn buildAlone(Type type, Hir.Expr fixture);

    /** What came of building one value as its own type. */
    enum OnItsOwn {

        BUILT,

        REFUSED,

        /**
         * The type is not one a value is decoded as on its own — an optional, a tuple, a function —
         * so nothing was asked. Not a refusal: such a type is decoded by the value that holds it.
         */
        NO_DECODER_OF_ITS_OWN
    }

    /** What came of building one value. */
    sealed interface Built {

        /** It built, and this is what it came to. */
        record Value(ObservedValue observed) implements Built {}

        /** It did not, and why. Never a claim that no value of the shape can be built. */
        record Refused(String why) implements Built {}
    }
}
