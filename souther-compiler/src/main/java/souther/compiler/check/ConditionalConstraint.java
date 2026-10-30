package souther.compiler.check;

/**
 * A relation an operation guarantees of its answer where another relation holds: the remainder of
 * a floor division is not negative where the divisor is above nought.
 *
 * <p>Not an {@link NumericConstraint}. What the operation guarantees is the same statement
 * wherever it is read, but whether its condition holds is a question about the values the
 * arguments are — {@code Int.clamp(1, 10, n)} is above nought on every path — and about what the
 * path put them at. So the pair is read as a recipe is ({@link Derivation.GuaranteedWhere}): the
 * condition is asked of the arguments with whatever was derived of them taken in first, and the
 * consequence is stated where it holds. Taken in whatever the path, the consequence would be a
 * fact about a divisor that could be either side of nought.
 *
 * @param premise     what has to hold of the arguments, as a relation to nought
 * @param consequence what then holds of the answer
 */
record ConditionalConstraint(NumericConstraint premise, NumericConstraint consequence) {}
