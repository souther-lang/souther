package souther.compiler.inputs;

import souther.compiler.core.Core;

/**
 * A value a name stands for, and what that value is read in.
 *
 * <p>The two travel together because they are one answer. A value stands for the name in the
 * environment the binding was made in, which is not always the one the name was read in; handed the
 * expression alone, each reader supplies an environment of its own, and two readers that supply
 * different ones are two accounts of what the name means.
 *
 * <p>One type rather than a pair written out at each place that needs it. A name standing for one
 * value and a name standing for one of several are the same kind of answer differing in how many
 * there are ({@link ReadMeaning.Through}, {@link ReadMeaning.OneOf}), and a plurality that dropped
 * the environment would be the pairing holding for one value and not for several — which is the
 * distinction being made by how many there happen to be.
 *
 * <p>Today the two environments cannot be told apart and a caller hands back the one it was given.
 * What makes that one fact rather than a coincidence repeated at each caller is that it is carried
 * here.
 */
public record Denotation(Core value, InputReads at) {

    public Denotation {
        java.util.Objects.requireNonNull(value, "a name stands for a value");
        java.util.Objects.requireNonNull(at, "and the value is read in something");
    }
}
