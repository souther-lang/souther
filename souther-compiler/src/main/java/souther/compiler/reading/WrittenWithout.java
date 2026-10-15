package souther.compiler.reading;

import souther.compiler.types.ConstructOccurrence;

import java.util.Objects;

/**
 * Something that holds on a way and is not written on it: a run down the way decided more than the
 * way says, and this is what it decided past it.
 *
 * <p>Told apart because they are short of different things. A step this reading has no words for
 * is a decision about the inputs nobody wrote down, which may be about any position. Being inside a
 * function value is short only of what the function was called with: where every call of it is an
 * operation applying it once to each element of a container the input holds, that is which element
 * a run handed it, and nothing else about the inputs — so the way says all a run down it decided
 * within one application, and a reader that knows the function is called so can read it whole.
 */
public sealed interface WrittenWithout {

    /** A step on the way this reading has no words for, or a bound it stopped reading the way at. */
    record AStep(PathAccess.Unsupported.Why why) implements WrittenWithout {

        public AStep {
            Objects.requireNonNull(why, "a step is left unsaid for a reason");
        }
    }

    /**
     * The way runs inside a function value to the fork at {@code fork}, which is taken where
     * something calls the function and is decided under whatever it was called with.
     *
     * <p>The fork and not the function: the reading that knows how the function is called reads
     * the tree where the language's operations stand, and a fork is what the two trees agree about
     * ({@link souther.compiler.types.ModelOccurrence}). A function value the operations are expanded
     * into is no function that tree holds.
     */
    record InAFunction(ConstructOccurrence fork) implements WrittenWithout {

        public InAFunction {
            Objects.requireNonNull(fork, "a way inside a function value goes to some fork");
        }
    }
}
