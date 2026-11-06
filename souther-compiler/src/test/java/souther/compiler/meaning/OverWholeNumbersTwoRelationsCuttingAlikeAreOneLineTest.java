package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two relations of one form are one line where they hold alike: where every number they are over
 * is whole, at whatever scale and with whatever ratios for weights, and whichever of at-least and
 * above each was written as, they are one line exactly where no whole numbers tell them apart;
 * where one of the numbers is not known to be whole, exactly where one is the other at a positive
 * scale.
 *
 * <p>Held against the rows themselves: every pair of relations over a grid of forms, each read as
 * one line or two, against whether some point tells the two apart — a point of whole numbers
 * where both are over whole numbers, and of every ratio otherwise, which is a positive scale.
 *
 * <p>A number is whole by what the input measures it on, or by what it is: {@code x} is whole as
 * the input measures it, {@code y} is whole only where the input is said to measure it so, and
 * {@code n}, how many of two statements hold, is whole whatever the input says.
 */
class OverWholeNumbersTwoRelationsCuttingAlikeAreOneLineTest {

    private static final NumericTerm X_TERM = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final Quantity X = new DecisionAtom.OfTheInput(X_TERM);
    private static final Quantity Y =
            new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("y")));
    private static final Quantity N = new Quantity.HowManyHold(List.of(
            positive("p"), positive("q")));

    /** Whether the input measures {@code term} in whole numbers, where it measures {@code x} so
     *  and nothing else. */
    private static boolean onlyX(NumericTerm term) {
        return term.equals(X_TERM);
    }

    /**
     * {@code first · a + second · b + constant} above or at nought, held, each weight a number of
     * sixths, so a half, a third and two thirds are among them.
     */
    private record Written(Proposition.Compared stated, Quantity a, Quantity b, int first,
                           int second, int constant, boolean above) {

        boolean holdsAt(int atA, int atB) {
            int sixTimes = atA * first + atB * second + constant;
            return above ? sixTimes > 0 : sixTimes >= 0;
        }

        /** Over the same numbers, the one at a positive scale of the other. */
        boolean atAPositiveScaleOf(Written other) {
            return above == other.above && first * other.second == other.first * second
                    && first * other.constant == other.first * constant;
        }
    }

    private static Proposition.Compared positive(String name) {
        return new Proposition.Compared(new Relation.Affine(LinearForm.atom(
                new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of(name)))),
                Rel.GT), true);
    }

    private static ExactRatio sixths(int n) {
        return ExactRatio.of(BigInteger.valueOf(n), BigInteger.valueOf(6));
    }

    private static Written written(Quantity a, Quantity b, int first, int second, int constant,
                                   boolean above) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(a, sixths(first));
        if (second != 0) {
            coefs.put(b, sixths(second));
        }
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(sixths(constant), coefs), above ? Rel.GT : Rel.GE);
        return new Written(new Proposition.Compared(
                new Relation.Affine(one.form(), one.proposition()), one.holds()),
                a, b, first, second, constant, above);
    }

    /**
     * Every relation of a grid over {@code a} and {@code b}: {@code a} weighed by a half, one and
     * two, alone and beside {@code b} weighed by minus two thirds and by two; constants by halves
     * from minus one to one.
     */
    private static List<Written> grid(Quantity a, Quantity b) {
        List<Written> out = new ArrayList<>();
        for (int first : new int[] {3, 6, 12}) {
            for (int second : new int[] {0, -4, 12}) {
                for (int constant = -6; constant <= 6; constant += 3) {
                    out.add(written(a, b, first, second, constant, false));
                    out.add(written(a, b, first, second, constant, true));
                }
            }
        }
        return out;
    }

    /** How many lines the statement of either is read as. */
    private static int linesOfEither(Written one, Written other,
                                     Predicate<NumericTerm> measuredWhole) {
        return WhereEachLineDecides.in(Proposition.any(List.of(one.stated(), other.stated())),
                measuredWhole).size();
    }

    private static boolean aWholePointTellsThemApart(Written one, Written other) {
        for (int a = -8; a <= 8; a++) {
            for (int b = -8; b <= 8; b++) {
                if (one.holdsAt(a, b) != other.holdsAt(a, b)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Every pair of the grid read otherwise than {@code oneLine} says, spelled. */
    private static Set<String> readWrongly(List<Written> grid,
                                           Predicate<NumericTerm> measuredWhole,
                                           Predicate<Written> overWholeNumbers) {
        Set<String> wrong = new TreeSet<>();
        for (Written one : grid) {
            for (Written other : grid) {
                boolean bothWhole = overWholeNumbers.test(one) && overWholeNumbers.test(other);
                boolean oneLine = bothWhole ? !aWholePointTellsThemApart(one, other)
                        : one.atAPositiveScaleOf(other);
                if (linesOfEither(one, other, measuredWhole) != (oneLine ? 1 : 2)) {
                    wrong.add(one.stated().spelledOut() + " | " + other.stated().spelledOut());
                }
            }
        }
        return wrong;
    }

    @Test
    void overWholeNumbersOneLineExactlyWhereNoWholeNumbersTellThemApart() {
        assertEquals(Set.of(), readWrongly(grid(X, Y), _ -> true, _ -> true));
    }

    @Test
    void besideANumberNotKnownWholeOneLineExactlyWhereOneIsTheOtherAtAPositiveScale() {
        assertEquals(Set.of(), readWrongly(grid(X, Y),
                OverWholeNumbersTwoRelationsCuttingAlikeAreOneLineTest::onlyX,
                each -> each.second() == 0));
    }

    @Test
    void aCountIsWholeWhateverTheInputSays() {
        assertEquals(Set.of(), readWrongly(grid(N, X), term -> false,
                each -> each.second() == 0));
    }
}
