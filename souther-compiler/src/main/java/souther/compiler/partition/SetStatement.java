package souther.compiler.partition;

import souther.compiler.check.PredicateStatement;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.values.ValueSet;
import souther.compiler.values.ValuesAtLengths;
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
 * some strings on neither side: the strings of {@code notShown}, those of
 * {@code pastWhatIsWritten} and those of {@code notReached} ({@link #leftOpen}). Those are no
 * class of either side, and a reader is told they are left open rather than counted on the side
 * nothing showed them on — and why, which differs between the three: only the first are open for
 * the operations of the library.
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
 * @param pastWhatIsWritten the values of the true side's set longer than a value of the other side
 *                  can be written round them, each as long as it is left open at: open for the
 *                  longest string, and for no operation; none where every length is written
 * @param notReached the values of the lengths at which no run gets to the relation, each as long
 *                  as it is left open at: shown on neither side, because the relation is not
 *                  worked out for a string of that length; none where a run gets to it at every
 *                  length
 * @param operations the operations of the library that are why {@code notShown} holds the
 *                  strings it holds, by why: whose image over the strings of a side is shown only
 *                  where it is exact, and which a run is not shown to get past
 * @param notCounted the values holding so few or so many code points of a class that no run gets
 *                  to the relation with them, which are shown on neither side as the values of
 *                  {@code notReached} are; kept apart because a length bounds none of them
 */
public record SetStatement(NumericTerm.FromOnePosition term, ValuesAtLengths whenTrue,
                          ValuesAtLengths whenFalse, PredicateStatement statement,
                          PredicateOrigin origin, List<ValuesWithin> notShown,
                          List<ValuesWithin> pastWhatIsWritten, List<ValuesWithin> notReached,
                          BlockReason.OperationsNotShown operations,
                          List<NotCounted> notCounted) {

    /**
     * The values holding a number of code points of a class that no run gets to the relation
     * with.
     *
     * @param values the values
     * @param why    which numbers of the class they are open for
     */
    public record NotCounted(ValueSet values, BlockReason.CodePointsLeftOpen why) {

        public NotCounted {
            if (values == null || why == null) {
                throw new IllegalArgumentException("some values hold too few or too many");
            }
        }
    }

    public SetStatement {
        if (term == null || whenTrue == null || whenFalse == null
                || statement == null || origin == null || notShown == null
                || pastWhatIsWritten == null || notReached == null || operations == null
                || notCounted == null) {
            throw new IllegalArgumentException(
                    "a statement about a position names some values, and some rule made it");
        }
        notShown = List.copyOf(notShown);
        pastWhatIsWritten = List.copyOf(pastWhatIsWritten);
        notReached = List.copyOf(notReached);
        notCounted = List.copyOf(notCounted);
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
        this(term, whenTrue, whenFalse, statement, origin, notShown, List.of(), List.of(),
                BlockReason.OperationsNotShown.NONE, List.of());
    }

    /** The same statement of the same values, about the position {@code at}. */
    public SetStatement measuredAt(NumericTerm.FromOnePosition at) {
        return new SetStatement(at, whenTrue, whenFalse, statement, origin, notShown,
                pastWhatIsWritten, notReached, operations, notCounted);
    }

    /** Whether every value is shown on one side or the other. */
    public boolean showsEveryValue() {
        return leftOpen().isEmpty() && notCounted.isEmpty();
    }

    /**
     * The values shown on neither side: those of {@code notShown}, those longer than a value of
     * the other side is written round, and those of the lengths no run gets to the relation at.
     */
    public List<ValuesWithin> leftOpen() {
        List<ValuesWithin> out = new ArrayList<>(notShown);
        out.addAll(pastWhatIsWritten);
        out.addAll(notReached);
        return out;
    }
}
