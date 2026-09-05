package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.values.ValueSet;

/**
 * A set of a position's values told from the rest, with both sides worked out.
 *
 * <p>What a rule of a behavior does to the strings at a position. {@code String.startsWith("JP",
 * code)} divides what stands at {@code code} into the values that satisfy it and the values that do
 * not, and a run of the model is on one side or the other — so the two sides are two classes, and
 * the partition owes a row at each.
 *
 * <p><b>Both sides, and neither is derived from the other here.</b> A caller handed the set the rule
 * admits and left to work out the rest would be complementing a language, which is the expensive
 * operation and the one thing a plan exists to arrange rather than to do. Worse, it would be doing
 * it under whatever allowance it happened to hold. So both are asked for as plans, built together
 * under the one allowance the position's distinctions are bounded by, and arrive here already
 * settled — and "the values it admits are known and the rest are not" is a state that cannot be
 * spelled.
 *
 * @param term     the position this divides, which one position answers
 * @param whenTrue the values that satisfy the rule
 * @param whenFalse the values that do not
 * @param origin   which rule this is, which reading of it, and where a reader is sent to find it
 */
public record SetDivision(NumericTerm.FromOnePosition term, ValueSet whenTrue, ValueSet whenFalse,
                          PredicateOrigin origin) {

    public SetDivision {
        if (term == null || whenTrue == null || whenFalse == null || origin == null) {
            throw new IllegalArgumentException(
                    "a division of a position tells some values from the rest, and some rule said"
                            + " it");
        }
        // A rule that tells nothing from anything divides nothing. Published as a division, it
        // would put a class in the denominator that no value of the model is ever on one side of,
        // and every run would be owed a row for it.
        if (whenTrue.isEmpty() || whenFalse.isEmpty()) {
            throw new IllegalArgumentException(
                    "a rule that leaves one of its sides empty divides nothing: " + origin);
        }
    }
}
