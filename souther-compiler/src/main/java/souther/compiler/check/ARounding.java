package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.Objects;

/**
 * An application of an operation the library says rounds a number to a step, by what it hands
 * where the law puts the scale, the policy and the number.
 *
 * <p>What each case of the policy does is the law's, matched to the library's cases once where the
 * law was bound ({@link OperationFactBinder}), and asked here of a policy as it is written.
 *
 * @param scale   what it hands as the scale, or null where it rounds to a whole number and takes
 *                none
 * @param policy  what it hands as the policy
 * @param rounded what it hands as the number it rounds
 */
public record ARounding(Core scale, Core policy, Core rounded, Ways ways) {

    public ARounding {
        Objects.requireNonNull(policy, "a number is rounded some way");
        Objects.requireNonNull(rounded, "and a number is rounded");
        Objects.requireNonNull(ways, "by one of the ways the law knows");
    }

    /** What each case of a policy does, as the law bound them. */
    public interface Ways {

        /** The way {@code written} rounds, where it is a case of the policy, and null otherwise. */
        WholeRounding of(Core written);
    }

    /** The way {@code written} rounds, where it is a case of the policy, and null otherwise. */
    public WholeRounding wayOf(Core written) {
        return ways.of(written);
    }

    /**
     * {@code applied} read as a rounding to a step, or null where the library says no such thing
     * of what it applies, or it hands nothing where the law puts the policy or the number.
     */
    static ARounding of(AnOperationApplied applied, BoundOperationFact.RoundsToAStep rounds) {
        Core policy = applied.argument(rounds.mode());
        Core rounded = applied.argument(rounds.value());
        Core scale = rounds.scale() == null ? null : applied.argument(rounds.scale());
        if (policy == null || rounded == null || (rounds.scale() != null && scale == null)) {
            return null;
        }
        return new ARounding(scale, policy, rounded, rounds::wayOf);
    }
}
