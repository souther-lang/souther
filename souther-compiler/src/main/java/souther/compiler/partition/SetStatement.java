package souther.compiler.partition;

import souther.compiler.check.PredicateStatement;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.values.ValuesAtLengths;
import souther.compiler.values.ValuesWithin;

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
 * some strings on neither side, for one of two reasons that are told apart. The strings of
 * {@code notShown} are strings the rule is asked of and shows nothing of for the operations of the
 * library ({@link #leftOpen}): they are no class of either side, and a reader is told they are left
 * open rather than counted on the side nothing showed them on. The strings of {@code notReached}
 * are those no run gets to the rule with, because a guard on the way keeps them from it: the rule
 * is not asked of them, no row can put one to it, and the rule that keeps them away is the one that
 * is owed a row there. They are not open, and are no class of this rule.
 *
 * <p><b>Each side is a set and the lengths of its values.</b> A length is a number of a string and
 * not a set of strings, so a side holding the strings of a set at some lengths is the set and the
 * lengths, whatever lengths those are: made into one set of strings they would be a machine as
 * long as the longest of them, and a long one is past what this compiler builds. The strings
 * shorter than some fewest code points or longer than some most are two runs of lengths and one
 * side.
 *
 * @param term      the position it is about, which one position answers
 * @param whenTrue  the values shown to satisfy the rule, a length and all
 * @param whenFalse the values shown not to, a length and all
 * @param statement what the rule states, in the words the model states it in
 * @param origin    which rule this is, which reading of it, and where a reader is sent to find it
 * @param notShown  the values shown on neither side for {@code operations}, each as long as it is
 *                  left open at; none where every value is shown on one
 * @param notReached the values no run gets to the relation with, each as long as it is kept from
 *                  it at: those of the lengths a guard on the way leaves out, and those holding so
 *                  few or so many code points of a class that the guard leaves them out, which no
 *                  length bounds; none where a run gets to it with every value
 * @param operations the operations of the library that are why {@code notShown} holds the
 *                  strings it holds, by why: whose image over the strings of a side is shown only
 *                  where it is exact, and which a run is not shown to get past
 */
public record SetStatement(NumericTerm.FromOnePosition term, ValuesAtLengths whenTrue,
                          ValuesAtLengths whenFalse, PredicateStatement statement,
                          PredicateOrigin origin, List<ValuesWithin> notShown,
                          List<ValuesWithin> notReached,
                          BlockReason.OperationsNotShown operations) {

    public SetStatement {
        if (term == null || whenTrue == null || whenFalse == null
                || statement == null || origin == null || notShown == null
                || notReached == null || operations == null) {
            throw new IllegalArgumentException(
                    "a statement about a position names some values, and some rule made it");
        }
        notShown = List.copyOf(notShown);
        notReached = List.copyOf(notReached);
        // Whether the two sides hold anything is not asked here, and cannot be. What a rule leaves
        // is a set of every string there is; what the position holds is what its declarations left
        // it — so a side inhabited among the strings can be empty at the position, and one empty
        // among them cannot be inhabited there. Which of those a rule is, is a question about the
        // position's values, and it is asked where they are known ({@link Classing}).
    }

    /** A rule that shows its values at every length a run gets to it at, and whose open values are
     *  open for no operation's image. */
    public SetStatement(NumericTerm.FromOnePosition term, ValuesAtLengths whenTrue,
                        ValuesAtLengths whenFalse, PredicateStatement statement,
                        PredicateOrigin origin, List<ValuesWithin> notShown) {
        this(term, whenTrue, whenFalse, statement, origin, notShown, List.of(),
                BlockReason.OperationsNotShown.NONE);
    }

    /** The same statement of the same values, about the position {@code at}. */
    public SetStatement measuredAt(NumericTerm.FromOnePosition at) {
        return new SetStatement(at, whenTrue, whenFalse, statement, origin, notShown,
                notReached, operations);
    }

    /** Whether every value the rule is asked of is shown on one side or the other. */
    public boolean showsEveryValue() {
        return notShown.isEmpty();
    }
}
