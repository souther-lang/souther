package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionBounds;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.ValueName;
import souther.compiler.values.TextExtents;
import souther.compiler.values.ValueSet;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.IntPredicate;

/**
 * What the strings an input holds reach, asked of the positions and never of an axis.
 *
 * <p>A line is drawn at a number by the rules around a string, which know nothing of the format
 * the string is in. Whether a row can be written at an edge on that number is a question about the
 * strings the position holds: a format leaves some lengths out, a set of every string but a few
 * leaves out the one string of a length, and a position none of whose strings is a value leaves
 * the input no value to write. Held by position, it is the same answer for an axis a declaration
 * measured and one a body measured for the first time.
 *
 * <p>Worked out when the input is read and held as the facts it comes to, not as the sets it was
 * worked out from: this travels in an answer, whose equality is what a later reading is compared
 * on, and a language is a machine nobody compares.
 *
 * <p>The strings of a position are a bound on its values ({@link TextExtents}), so what is
 * established here is a claim that every such number is the number of some value, and a number not
 * shown to be is not proved writable. That is not a claim that no value has it.
 *
 * @param inputHoldsAValue whether every position is shown to hold a value. A row at an edge is a
 *                         whole value of the input, so a position that may hold none leaves every
 *                         edge of it unproved
 * @param unrestricted     the positions whose strings no rule restricts, which have a value of
 *                         every length, every sum of code points and every count of a class
 * @param lengthsReached   the lengths of a position the rules leave it, where every one is the
 *                         length of some value
 */
public record StringsReached(boolean inputHoldsAValue, Set<TermPath> unrestricted,
                             Set<NumericTerm> lengthsReached) {

    /** An input none of whose positions is a string. */
    public static final StringsReached NONE = new StringsReached(true, Set.of(), Set.of());

    public StringsReached {
        unrestricted = Set.copyOf(unrestricted);
        lengthsReached = Set.copyOf(lengthsReached);
    }

    /** What the strings at {@code positions} reach. */
    static StringsReached of(List<Position> positions) {
        boolean holds = true;
        Set<TermPath> unrestricted = new LinkedHashSet<>();
        Set<NumericTerm> lengths = new LinkedHashSet<>();
        for (Position each : positions) {
            ValueSet admitted = each.admitted().approximation();
            holds &= TextExtents.shownToHoldAValue(admitted);
            if (TextExtents.reachesEveryCount(admitted)) {
                unrestricted.add(each.path());
            }
            for (PositionBounds bounds : each.bounds()) {
                if (isLength(bounds.term()) && reachesEveryLengthLeft(admitted, bounds)) {
                    lengths.add(bounds.term());
                }
            }
        }
        return new StringsReached(holds, unrestricted, lengths);
    }

    /**
     * Whether every number {@code term} can take of the strings where it is read is the number of
     * some value there. True of a term that is not a number of a string: what it reaches is
     * another reading's.
     */
    public boolean reaches(NumericTerm term) {
        if (isLength(term)) {
            return lengthsReached.contains(term)
                    || unrestricted.contains(((NumericTerm.FromOnePosition) term).position());
        }
        // Any other number a string operation answers is shown only of strings nothing restricts.
        if (term instanceof NumericTerm.CodePointClassCount
                || term instanceof NumericTerm.CodePointValueSum
                || (term instanceof NumericTerm.TakenOf other
                        && other.operation().alias().equals("String"))) {
            return unrestricted.contains(((NumericTerm.FromOnePosition) term).position());
        }
        return true;
    }

    private static boolean isLength(NumericTerm term) {
        return term instanceof NumericTerm.TakenOf taken
                && taken.operation().equals(ValueName.Stdlib.operation("String", "length"));
    }

    /**
     * Whether every length the rules leave the number {@code bounds} is about is the length of a
     * value of {@code at}.
     *
     * <p>The lengths the rules leave are what the numeric reading holds of it, which is the lengths
     * a rule written as a bound on the length excludes and nothing a format excludes: a format is
     * a bound on the strings, and the numbers around it do not know it. An edge can be at any of
     * them, so each has to be a length some value has.
     */
    private static boolean reachesEveryLengthLeft(ValueSet at, PositionBounds bounds) {
        NumericDomain.Bounds left =
                bounds.rangeLeft() == null ? NumericDomain.Bounds.OPEN : bounds.rangeLeft();
        IntPredicate wanted = each -> each >= 0 && left.admits(ExactRatio.of(each));
        return TextExtents.reachesEveryLength(at, wanted, left.max() == null);
    }
}
