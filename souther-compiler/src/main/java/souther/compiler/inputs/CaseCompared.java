package souther.compiler.inputs;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * A comparison of a value of a sum with one of its cases that is the whole of one value, read as
 * which case the value is.
 *
 * <p>{@code reason == WrongPassword} asks whether the reason is a {@code WrongPassword}, which is
 * what an arm of a {@code match} on it asks. The cases of an enumeration are ordered too, by the
 * order they are declared in, but an equality does not ask that order anything: the case declared
 * after {@code WrongPassword} is no nearer to it than the one declared last. Read as a line on the
 * order, the comparison would owe rows beside a value nobody wrote it about, and would move them
 * whenever the declaration was reordered.
 *
 * <p>Only a case that is one value. A case holding a record is many values, and comparing with one
 * of them asks which of them the value is as well as which case.
 *
 * @param at      the position the value of the sum stands at
 * @param named   the case it is compared with
 * @param leaves  every case a value at {@code at} may be, {@code named} among them
 * @param heldAtTheCase whether the comparison comes out true where the value is {@code named}:
 *                true for {@code ==}, false for {@code /=}
 */
public record CaseCompared(TermPath at, TypeSymbol named, List<TypeSymbol> leaves,
                           boolean heldAtTheCase) {

    public CaseCompared {
        leaves = List.copyOf(leaves);
        if (!leaves.contains(named)) {
            throw new IllegalArgumentException(
                    named + " is compared with a value at " + at + " that cannot be it");
        }
    }

    /**
     * What {@code comparison} asks, or null where it is no such comparison: one that does not name
     * one value, neither side at a position, the other no case written with nothing in it, or a
     * case a value at the position cannot be.
     *
     * <p>Either side may be the position. Both are read where they stand, so a case given a name
     * is the case it names.
     */
    public static CaseCompared of(StatedComparison comparison, InputReading read,
                                  InputReads reads) {
        if (!(comparison.claim() instanceof ComparisonClaim.Singled singled)) {
            return null;
        }
        CaseCompared left = oneWayRound(comparison.left(), comparison.right(), singled, read, reads);
        return left != null ? left
                : oneWayRound(comparison.right(), comparison.left(), singled, read, reads);
    }

    /** The same of {@code e}, where it is a comparison ({@link BooleanMeaning#asAComparison}). */
    public static CaseCompared of(Core e, InputReading read, InputReads reads) {
        return BooleanMeaning.asAComparison(e).map(stated -> of(stated, read, reads)).orElse(null);
    }

    private static CaseCompared oneWayRound(Core value, Core written, ComparisonClaim.Singled singled,
                                            InputReading read, InputReads reads) {
        if (!(reads.pathOf(value, read.newtypes()) instanceof PathResolution.At(TermPath at))) {
            return null;
        }
        // Followed as far as a value an order would read it ({@link ComparedNumber}), so that a name
        // for a choice of cases, read under the arm the walk took, is the case that arm answers.
        if (!(Core.withoutStanding(reads.standingValue(written, read.symbols(), read.newtypes())
                .value()) instanceof Core.UnitValue unit)) {
            return null;
        }
        // The cases under the last name the position wears, which are what a value there is.
        List<TypeSymbol> leaves = read.declared().leavesAt(at)
                .map(List::getLast).orElse(List.of());
        return leaves.contains(unit.data())
                ? new CaseCompared(at, unit.data(), leaves, singled.holdsAtTheValue()) : null;
    }

    /** The case compared with, as what the comparison holding at it leaves the value. One value,
     *  since a case written with nothing in it is the whole of one. */
    public CasesLeft selected() {
        return CasesLeft.of(Refinement.of(new Case.SumCase(named, true)));
    }

    /** The cases the value may be where the comparison came out {@code held}; none where no value
     *  at the position comes out that way. */
    public List<TypeSymbol> leavesWhere(boolean held) {
        return held == heldAtTheCase ? List.of(named)
                : leaves.stream().filter(each -> !each.equals(named)).toList();
    }
}
