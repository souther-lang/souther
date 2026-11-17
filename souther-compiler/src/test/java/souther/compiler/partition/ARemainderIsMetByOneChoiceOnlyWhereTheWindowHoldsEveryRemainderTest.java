package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.UndividedByARelation.WholeEnds;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One number is chosen to bring a form to a remainder, for every row of the others, where the
 * values of it that keep the form inside the type are as many as there are remainders — and
 * nowhere else. Each case is one thing that moves that count, the form {@code d - p} by seven
 * inside a type from -100 to 100 unless a case says another.
 */
class ARemainderIsMetByOneChoiceOnlyWhereTheWindowHoldsEveryRemainderTest {

    private static final NumericTerm P = term("p");
    private static final NumericTerm D = term("d");
    private static final NumericTerm N = term("n");

    @Test
    void aPivotWhoseValuesInTheTypeAreAsManyAsTheRemaindersMeetsEveryOne() {
        assertTrue(prove(ends(-20, 20), kept(0, 10), List.of(0), -1, 1).isPresent());
    }

    @Test
    void aPivotWithFewerValuesThanThereAreRemaindersDoesNot() {
        assertTrue(prove(ends(0, 5), kept(0, 10), List.of(0), -1, 1).isEmpty());
        assertTrue(prove(ends(0, 6), kept(0, 10), List.of(0), -1, 1).isPresent());
    }

    /** Stepping the form by two, the values in a window are as many as it is wide only for some
     *  remainders of the rest. */
    @Test
    void aPivotWeighingMoreThanOneIsNotTaken() {
        assertTrue(prove(ends(-20, 20), kept(0, 10), List.of(0), -2, 1).isEmpty());
    }

    /** A statement moved a step further needs the type's window a step wider. */
    @Test
    void statementsMovedApartNeedTheTypesWindowWider() {
        assertTrue(RemainderCoverage.prove(P, ends(-10, 10), Map.of(D, kept(0, 0)),
                form(-1, 1, 0), List.of(big(0)), big(7), List.of(), big(-3), big(3)).isPresent());
        assertTrue(RemainderCoverage.prove(P, ends(-10, 10), Map.of(D, kept(0, 0)),
                form(-1, 1, 0), List.of(big(0), big(1)), big(7), List.of(), big(-3), big(3))
                .isEmpty());
    }

    /** What the run narrows of the numbers alone bounds what they come to, and stays. */
    @Test
    void aNarrowingOfTheKeptNumbersAloneBoundsTheirSumAndStaysInTheRegion() {
        LinearForm<NumericTerm> dividend = LinearForm.<NumericTerm>atom(D)
                .plus(LinearForm.atom(N)).orNull();
        Map<NumericTerm, RemainderCoverage.Other> others = new LinkedHashMap<>();
        others.put(D, kept(-1000, 1000));
        others.put(N, kept(-1000, 1000));
        List<TakenConstraint> premise = List.of(
                constraint(Rel.LE, -100, D, 1, N, 1), constraint(Rel.GE, 100, D, 1, N, 1));
        LinearForm<NumericTerm> form = withPivot(dividend, -1);
        assertTrue(RemainderCoverage.prove(P, ends(-100, 100), others, form, List.of(big(0)),
                big(7), List.of(), big(-100), big(100)).isEmpty());
        Optional<RemainderCoverage.Proof> proof = RemainderCoverage.prove(P, ends(-100, 100),
                others, form, List.of(big(0)), big(7), premise, big(-100), big(100));
        assertTrue(proof.isPresent());
        assertEquals(List.of(), proof.get().narrowingsMet());
    }

    /** What ends the form whole narrows where the pivot may be put, and comes out with the
     *  statements. */
    @Test
    void aNarrowingOfTheWholeFormNarrowsTheWindowAndComesOut() {
        List<TakenConstraint> sevenValues = List.of(
                constraint(Rel.LE, -3, D, 1, P, -1), constraint(Rel.GE, 3, D, 1, P, -1));
        Optional<RemainderCoverage.Proof> proof = RemainderCoverage.prove(P, ends(-100, 100),
                Map.of(D, kept(0, 10)), form(-1, 1, 0), List.of(big(0)), big(7), sevenValues,
                big(-100), big(100));
        assertTrue(proof.isPresent());
        assertEquals(sevenValues, proof.get().narrowingsMet());
        List<TakenConstraint> sixValues = List.of(
                constraint(Rel.LE, -2, D, 1, P, -1), constraint(Rel.GE, 3, D, 1, P, -1));
        assertTrue(RemainderCoverage.prove(P, ends(-100, 100), Map.of(D, kept(0, 10)),
                form(-1, 1, 0), List.of(big(0)), big(7), sixValues, big(-100), big(100))
                .isEmpty());
    }

    /** What the run narrows of the pivot alone narrows where it may be put. */
    @Test
    void aNarrowingOfThePivotAloneNarrowsItsValues() {
        List<TakenConstraint> belowMinusNinetyFive = List.of(constraint(Rel.LE, 95, P, 1));
        assertTrue(RemainderCoverage.prove(P, ends(-100, 100), Map.of(D, kept(0, 10)),
                form(-1, 1, 0), List.of(big(0)), big(7), belowMinusNinetyFive, big(-100),
                big(100)).isEmpty());
    }

    @Test
    void aNumberChosenAtNoughtMustTakeNought() {
        LinearForm<NumericTerm> dividend = withPivot(LinearForm.<NumericTerm>atom(D)
                .plus(LinearForm.atom(N)).orNull(), -1);
        Map<NumericTerm, RemainderCoverage.Other> takesNought = new LinkedHashMap<>();
        takesNought.put(D, kept(0, 10));
        takesNought.put(N, new RemainderCoverage.Other(ends(-5, 5), true));
        Map<NumericTerm, RemainderCoverage.Other> doesNot = new LinkedHashMap<>();
        doesNot.put(D, kept(0, 10));
        doesNot.put(N, new RemainderCoverage.Other(ends(1, 5), true));
        assertTrue(RemainderCoverage.prove(P, ends(-20, 20), takesNought, dividend,
                List.of(big(0)), big(7), List.of(), big(-100), big(100)).isPresent());
        assertTrue(RemainderCoverage.prove(P, ends(-20, 20), doesNot, dividend,
                List.of(big(0)), big(7), List.of(), big(-100), big(100)).isEmpty());
    }

    /** The program adds the numbers one at a time: a sum of the pivot and some of the others is a
     *  stop this does not look at. */
    @Test
    void aNarrowingOfAPrefixOfTheFormIsNotTaken() {
        LinearForm<NumericTerm> dividend = withPivot(LinearForm.<NumericTerm>atom(D)
                .plus(LinearForm.atom(N)).orNull(), -1);
        Map<NumericTerm, RemainderCoverage.Other> others = new LinkedHashMap<>();
        others.put(D, kept(0, 10));
        others.put(N, kept(0, 10));
        List<TakenConstraint> prefix = List.of(constraint(Rel.LE, -5, D, 1, P, -1));
        assertTrue(RemainderCoverage.prove(P, ends(-100, 100), others, dividend,
                List.of(big(0)), big(7), prefix, big(-100), big(100)).isEmpty());
    }

    private static Optional<RemainderCoverage.Proof> prove(WholeEnds pivotEnds,
                                                           RemainderCoverage.Other other,
                                                           List<Integer> moves, int onPivot,
                                                           int onKept) {
        return RemainderCoverage.prove(P, pivotEnds, Map.of(D, other), form(onPivot, onKept, 0),
                moves.stream().map(each -> big(each)).toList(), big(7), List.of(), big(-100),
                big(100));
    }

    private static LinearForm<NumericTerm> form(int onPivot, int onKept, int constant) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(P, ExactRatio.of(onPivot));
        coefs.put(D, ExactRatio.of(onKept));
        return new LinearForm<>(ExactRatio.of(constant), coefs);
    }

    private static LinearForm<NumericTerm> withPivot(LinearForm<NumericTerm> form, int onPivot) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>(form.coefs());
        coefs.put(P, ExactRatio.of(onPivot));
        return new LinearForm<>(form.constant(), coefs);
    }

    /** {@code constant + weight * term + ... rel 0}. */
    private static TakenConstraint constraint(Rel rel, int constant, Object... termsAndWeights) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (int i = 0; i < termsAndWeights.length; i += 2) {
            coefs.put((NumericTerm) termsAndWeights[i],
                    ExactRatio.of((Integer) termsAndWeights[i + 1]));
        }
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant), coefs), rel);
    }

    private static RemainderCoverage.Other kept(int low, int high) {
        return new RemainderCoverage.Other(ends(low, high), false);
    }

    private static WholeEnds ends(int low, int high) {
        return new WholeEnds(big(low), big(high));
    }

    private static NumericTerm term(String name) {
        return new NumericTerm.ValueOf(TermPath.of(name));
    }

    private static BigInteger big(long value) {
        return BigInteger.valueOf(value);
    }
}
