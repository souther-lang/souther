package souther.compiler.execute;

import souther.compiler.ast.Hir;
import souther.compiler.check.BoundaryInput;
import souther.compiler.observe.ObservedValue;

import java.util.Optional;

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

    /** Whether the value was refused, for a caller that has nothing to do with what it is. */
    default Optional<String> refuse(BoundaryInput at, Hir.Expr fixture) {
        return build(at, fixture) instanceof Built.Refused refused
                ? Optional.of(refused.why()) : Optional.empty();
    }

    /** What came of building one value. */
    sealed interface Built {

        /** It built, and this is what it came to. */
        record Value(ObservedValue observed) implements Built {}

        /** It did not, and why. Never a claim that no value of the shape can be built. */
        record Refused(String why) implements Built {}
    }
}
