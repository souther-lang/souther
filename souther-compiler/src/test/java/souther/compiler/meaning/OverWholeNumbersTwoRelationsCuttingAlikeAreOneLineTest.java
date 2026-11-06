package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two relations of one form are one line where they hold alike: over whole numbers, at whatever
 * scale and whichever of at-least and above each was written as, they are one line exactly where
 * no whole number tells them apart; over numbers not known to be whole, exactly where one is the
 * other at a positive scale.
 *
 * <p>Held against the rows themselves: every pair of relations over a grid of forms, each read as
 * one line or two, against whether some point of the grid holds one and not the other.
 */
class OverWholeNumbersTwoRelationsCuttingAlikeAreOneLineTest {

    private static final DecisionAtom X = atom("x");
    private static final DecisionAtom Y = atom("y");

    /** What each relation is, and how it is read at a row. */
    private record Written(Proposition.Compared stated, int x, int y, int constant, boolean above) {

        boolean holdsAt(int atX, int atY) {
            int value = x * atX + y * atY + constant;
            return above ? value > 0 : value >= 0;
        }
    }

    private static DecisionAtom atom(String name) {
        return new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of(name)));
    }

    /** {@code x·X + y·Y + constant} above or at nought, held. */
    private static Written written(int x, int y, int constant, boolean above) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(X, ExactRatio.of(x));
        if (y != 0) {
            coefs.put(Y, ExactRatio.of(y));
        }
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.of(constant), coefs), above ? Rel.GT : Rel.GE);
        return new Written(new Proposition.Compared(
                new Relation.Affine(one.form(), one.proposition()), one.holds()),
                x, y, constant, above);
    }

    /**
     * Every relation of the grid: the weight of {@code X} above nought, so it faces one way; one
     * and two of it, alone and beside two of {@code Y}, so a form at a scale and one whose
     * weights share a divisor are among them.
     */
    private static List<Written> grid() {
        List<Written> out = new ArrayList<>();
        for (int x = 1; x <= 2; x++) {
            for (int y : new int[] {0, 2}) {
                for (int constant = -4; constant <= 4; constant++) {
                    out.add(written(x, y, constant, false));
                    out.add(written(x, y, constant, true));
                }
            }
        }
        return out;
    }

    /** How many lines the statement of either is read as. */
    private static int linesOfEither(Written one, Written other, WholeNumbers whole) {
        return WhereEachLineDecides.in(Proposition.any(List.of(one.stated(), other.stated())),
                whole).size();
    }

    private static boolean aWholePointTellsThemApart(Written one, Written other) {
        for (int x = -6; x <= 6; x++) {
            for (int y = -6; y <= 6; y++) {
                if (one.holdsAt(x, y) != other.holdsAt(x, y)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Whether one is the other at a positive scale, which every number holds alike. */
    private static boolean atAPositiveScale(Written one, Written other) {
        return one.above() == other.above()
                && one.x() * other.y() == other.x() * one.y()
                && one.x() * other.constant() == other.x() * one.constant();
    }

    @Test
    void overWholeNumbersOneLineExactlyWhereNoWholeNumberTellsThemApart() {
        WholeNumbers whole = _ -> true;
        Set<String> wrong = new TreeSet<>();
        for (Written one : grid()) {
            for (Written other : grid()) {
                int expected = aWholePointTellsThemApart(one, other) ? 2 : 1;
                if (linesOfEither(one, other, whole) != expected) {
                    wrong.add(one.stated().spelledOut() + " | " + other.stated().spelledOut());
                }
            }
        }
        assertEquals(Set.of(), wrong);
    }

    @Test
    void overNumbersNotKnownWholeOneLineExactlyWhereOneIsTheOtherAtAPositiveScale() {
        Set<String> wrong = grid().stream().flatMap(one -> grid().stream()
                .filter(other -> linesOfEither(one, other, WholeNumbers.NONE)
                        != (atAPositiveScale(one, other) ? 1 : 2))
                .map(other -> one.stated().spelledOut() + " | " + other.stated().spelledOut()))
                .collect(Collectors.toCollection(TreeSet::new));
        assertEquals(Set.of(), wrong);
    }
}
