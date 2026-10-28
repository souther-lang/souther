package souther.compiler.partition;

import souther.compiler.check.PredicateStatement;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.values.ValueSet;
import souther.compiler.values.ValuesWithin;

import java.util.ArrayList;
import java.util.List;

/**
 * What a rule of a behavior states about the strings at a position, as the values on either side.
 *
 * <p>A statement and not yet a division, which is the whole of the difference. {@code
 * String.startsWith("JP", code)} names the strings that satisfy it and the strings that do not; what
 * the position holds is what its own declarations left it, so whether the two sides are two classes
 * of this position is settled where its values are known ({@link Classing}) and is not settled here.
 * Called a division, the type would say of every value it holds a thing that is true of some of
 * them — and the reading that publishes one has no way to know which.
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
 * <p><b>And where neither side is shown.</b> A rule read off what another value can hold may show
 * some strings on neither side: the strings of {@code notShown}, and those of the set
 * {@code whenTrue} is of that are longer than it is shown at ({@link #leftOpen}). Those are no
 * class of either side, and a reader is told they are left open rather than counted on the side
 * nothing showed them on.
 *
 * @param term      the position it is about, which one position answers
 * @param whenTrue  the values shown to satisfy the rule, a length and all
 * @param whenFalse the values that do not
 * @param statement what the rule states, in the words the model states it in
 * @param origin    which rule this is, which reading of it, and where a reader is sent to find it
 * @param notShown  the values shown on neither side, whatever their length; none where every value
 *                  is shown on one
 */
public record SetStatement(NumericTerm.FromOnePosition term, ValuesWithin whenTrue,
                          ValueSet whenFalse, PredicateStatement statement,
                          PredicateOrigin origin, ValueSet notShown) {

    public SetStatement {
        if (term == null || whenTrue == null || whenFalse == null
                || statement == null || origin == null || notShown == null) {
            throw new IllegalArgumentException(
                    "a statement about a position names some values, and some rule made it");
        }
        // Whether the two sides hold anything is not asked here, and cannot be. What a rule leaves
        // is a set of every string there is; what the position holds is what its declarations left
        // it — so a side inhabited among the strings can be empty at the position, and one empty
        // among them cannot be inhabited there. Which of those a rule is, is a question about the
        // position's values, and it is asked where they are known ({@link Classing}).
    }

    /** Whether every value is shown on one side or the other. */
    public boolean showsEveryValue() {
        return leftOpen().isEmpty();
    }

    /**
     * The values shown on neither side: those of {@code notShown}, and those of the set the true
     * side is of past the length it is shown at. A string shorter than that is on one side.
     */
    public List<ValuesWithin> leftOpen() {
        List<ValuesWithin> out = new ArrayList<>();
        if (!notShown.isEmpty()) {
            out.add(ValuesWithin.all(notShown));
        }
        if (whenTrue.longest() != null) {
            out.add(ValuesWithin.longerThan(whenTrue.values(), whenTrue.longest()));
        }
        return out;
    }
}
