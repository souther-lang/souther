package souther.compiler.partition;

import souther.compiler.check.PredicateStatement;
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
 * <p><b>What it states and which rule it is are two things and both travel.</b> A class this leaves
 * is called by what a value in it satisfies, which is the statement; which rule of the model
 * produced the division, and which reading of that rule, is the origin. Two copies of one helper
 * divide two positions by one statement under two origins, and a reader given only the second would
 * have to name a class after where a rule was written.
 *
 * @param term      the position this divides, which one position answers
 * @param whenTrue  the values that satisfy the rule
 * @param whenFalse the values that do not
 * @param statement what the rule states, in the words the model states it in
 * @param origin    which rule this is, which reading of it, and where a reader is sent to find it
 */
public record SetDivision(NumericTerm.FromOnePosition term, ValueSet whenTrue, ValueSet whenFalse,
                          PredicateStatement statement, PredicateOrigin origin) {

    public SetDivision {
        if (term == null || whenTrue == null || whenFalse == null
                || statement == null || origin == null) {
            throw new IllegalArgumentException(
                    "a division of a position tells some values from the rest, and some rule said"
                            + " it");
        }
        // Whether the two sides hold anything is not asked here, and cannot be. What a rule leaves
        // is a set of every string there is; what the position holds is what its declarations left
        // it — so a side inhabited among the strings can be empty at the position, and one empty
        // among them cannot be inhabited there. Which of those a rule is, is a question about the
        // position's values, and it is asked where they are known ({@link Classing}).
    }
}
