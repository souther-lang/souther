package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a line at a remainder is proved to decide in none of the cases it is said for, no two
 * inputs, one holding the line and one failing it, meet the same case.
 *
 * <p>Each case below carries one rule of the proof: what a condition holds at, its denial and its
 * offset, how an {@code All} and an {@code Any} of conditions hold, what a choice leaves open and
 * what a case held together fixes, and what is not read. The inputs are the numbers a remainder by
 * three tells apart twice over, tried whole by a count worked out here and not by the proof.
 */
class NoCaseCrossesProvesNoneWhereAPairOfRowsMeetsOneCaseTest {

    private static final Quantity X = new DecisionAtom.OfTheInput(
            new NumericTerm.ValueOf(TermPath.of("x")));
    private static final Quantity Y = new DecisionAtom.OfTheInput(
            new NumericTerm.ValueOf(TermPath.of("y")));

    private static Proposition.Compared relation(Map<Quantity, Integer> coefs, int constant,
                                                 Rel rel, boolean holds) {
        Map<Quantity, ExactRatio> by = new LinkedHashMap<>();
        coefs.forEach((quantity, coef) -> by.put(quantity, ExactRatio.of(coef)));
        return new Proposition.Compared(new Relation.Affine(
                new LinearForm<>(ExactRatio.of(constant), by), rel), holds);
    }

    private static Quantity remainder(Quantity of, int by, int divisor) {
        return new Quantity.RemainderOfADividend(ValueName.Stdlib.operation("Int", "floorMod"),
                new LinearForm<>(ExactRatio.of(by), Map.of(of, ExactRatio.ONE)),
                BigInteger.valueOf(divisor));
    }

    /** What an input is: two numbers, each told apart by its remainder by three twice over. */
    private record Input(int x, int y) {}

    private static List<Input> everyInput() {
        List<Input> out = new ArrayList<>();
        for (int x = 0; x < 6; x++) {
            for (int y = 0; y < 6; y++) {
                out.add(new Input(x, y));
            }
        }
        return out;
    }

    // ---- what a condition holds of an input, worked out here and not by the proof ----

    private static long value(Quantity quantity, Input in) {
        if (quantity.equals(X)) {
            return in.x();
        }
        if (quantity.equals(Y)) {
            return in.y();
        }
        Quantity.RemainderOfADividend remainder = (Quantity.RemainderOfADividend) quantity;
        return Math.floorMod(form(remainder.dividend(), in), remainder.divisor().longValueExact());
    }

    private static long form(LinearForm<Quantity> form, Input in) {
        long sum = whole(form.constant());
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            sum += whole(each.getValue()) * value(each.getKey(), in);
        }
        return sum;
    }

    private static long whole(ExactRatio ratio) {
        return ((ExactAnswer.Held<BigInteger>) ratio.floor()).value().longValueExact();
    }

    private static boolean holds(Proposition p, Input in) {
        return switch (p) {
            case Proposition.Compared c -> {
                Relation.Affine affine = (Relation.Affine) c.relation();
                long form = form(affine.form(), in);
                boolean read = switch (affine.proposition()) {
                    case GE -> form >= 0;
                    case GT -> form > 0;
                    case LE -> form <= 0;
                    case LT -> form < 0;
                    case EQ -> form == 0;
                    case NE -> form != 0;
                };
                yield c.holds() == read;
            }
            case Proposition.All all -> all.parts().stream().allMatch(part -> holds(part, in));
            case Proposition.Any any -> any.parts().stream().anyMatch(part -> holds(part, in));
            default -> throw new IllegalArgumentException(p.toString());
        };
    }

    /** Whether some case of {@code cases} holds for both inputs: each of them chosen through
     *  alone where it is an alternative, every factor of one where it is held together. */
    private static boolean someCaseHoldsFor(DecidingCase.Cases cases, Input one, Input other,
                                            Map<Object, Boolean> memo) {
        Boolean known = memo.get(cases);
        if (known != null) {
            return known;
        }
        boolean out = switch (cases) {
            case DecidingCase.Cases.One c -> holds(c.condition(), one) && holds(c.condition(), other);
            case DecidingCase.Cases.EachOf each -> each.alternatives().stream()
                    .anyMatch(a -> someCaseHoldsFor(a, one, other, memo));
            case DecidingCase.Cases.Together together -> together.factors().stream()
                    .allMatch(a -> someCaseHoldsFor(a, one, other, memo));
            case DecidingCase.Cases.NotTakenApart _ -> true;
        };
        memo.put(cases, out);
        return out;
    }

    /** Whether two inputs, one holding {@code line} and one failing it, meet one case. */
    private static boolean someCaseCrosses(Proposition.Compared line, DecidingCase.Cases cases,
                                           List<Input> inputs) {
        for (Input holding : inputs) {
            if (!holds(line, holding)) {
                continue;
            }
            for (Input failing : inputs) {
                if (holds(line, failing)) {
                    continue;
                }
                if (someCaseHoldsFor(cases, holding, failing, new IdentityHashMap<>())) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean proves(Proposition.Compared line, DecidingCase.Cases cases) {
        return NoCaseCrosses.proves(line, new DecidingCase(line, cases), _ -> true);
    }

    private static Proposition.Compared remainderLine(int offset, int least) {
        return relation(Map.of(remainder(X, offset, 3), 1), -least, Rel.GE, true);
    }

    @Test
    void casesThatFixTheRemainderToOneSideOfTheLineAreProvedToHaveNoRowOnEachSide() {
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases cases = DecidingCase.Cases.together(List.of(
                new DecidingCase.Cases.One(relation(Map.of(remainder(X, 1, 3), 1), 0, Rel.EQ, true)),
                new DecidingCase.Cases.One(relation(Map.of(Y, 1), -2, Rel.GE, true))));

        assertFalse(someCaseCrosses(line, cases, everyInput()), "x + 1 is 0 mod 3, so x is 2");
        assertTrue(proves(line, cases));
    }

    @Test
    void casesThatLeaveBothSidesOfTheLineAreNotProved() {
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases cases = new DecidingCase.Cases.One(
                relation(Map.of(Y, 1), -2, Rel.GE, true));

        assertTrue(someCaseCrosses(line, cases, everyInput()));
        assertFalse(proves(line, cases));
    }

    @Test
    void whatOneAlternativeLeavesOpenIsLeftOpenByTheCasesThatChooseIt() {
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases fixed = new DecidingCase.Cases.One(
                relation(Map.of(remainder(X, 0, 3), 1), 0, Rel.EQ, true));
        DecidingCase.Cases open = new DecidingCase.Cases.One(
                relation(Map.of(Y, 1), -2, Rel.GE, true));
        DecidingCase.Cases cases = new DecidingCase.Cases.EachOf(List.of(fixed, open));

        assertTrue(someCaseCrosses(line, cases, everyInput()), "the second alternative");
        assertFalse(proves(line, cases));
    }

    @Test
    void aFactorThatFixesTheRemainderFixesItForTheWholeCase() {
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases fixed = new DecidingCase.Cases.One(
                relation(Map.of(remainder(X, 0, 3), 1), 0, Rel.EQ, true));
        DecidingCase.Cases open = new DecidingCase.Cases.EachOf(List.of(
                new DecidingCase.Cases.One(relation(Map.of(Y, 1), -2, Rel.GE, true)),
                new DecidingCase.Cases.One(relation(Map.of(Y, 1), -2, Rel.GE, false))));
        DecidingCase.Cases cases = DecidingCase.Cases.together(List.of(fixed, open));

        assertFalse(someCaseCrosses(line, cases, everyInput()));
        assertTrue(proves(line, cases));
    }

    @Test
    void casesNobodyTookApartAreNotProved() {
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases cases = new DecidingCase.Cases.NotTakenApart(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.atDeclared());

        assertTrue(someCaseCrosses(line, cases, everyInput()), "any two rows are of them");
        assertFalse(proves(line, cases));
    }

    @Test
    void theOffsetOfARemainderMovesTheResiduesItHoldsAt() {
        // (x + 1) mod 3 is at least 1 for x of 0 and 1, and the line holds at 0 alone: x of 0
        // and x of 1 are two rows of one case, one each side.
        Proposition.Compared line = relation(Map.of(remainder(X, 0, 3), 1), 0, Rel.EQ, true);
        DecidingCase.Cases cases = new DecidingCase.Cases.One(
                relation(Map.of(remainder(X, 1, 3), 1), -1, Rel.GE, true));

        assertTrue(someCaseCrosses(line, cases, everyInput()));
        assertFalse(proves(line, cases));
    }

    @Test
    void aConditionDeniedHoldsAtTheResiduesItsRelationDoesNot() {
        // Not (x mod 3 >= 1) is x of 0 mod 3, where the line x mod 3 >= 1 holds at no row.
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases cases = new DecidingCase.Cases.One(
                relation(Map.of(remainder(X, 0, 3), 1), -1, Rel.GE, false));

        assertFalse(someCaseCrosses(line, cases, everyInput()));
        assertTrue(proves(line, cases));
    }

    @Test
    void everyPartOfAConjunctionHoldsAndSomePartOfADisjunctionDoes() {
        Proposition.Compared line = remainderLine(0, 1);
        Proposition one = relation(Map.of(remainder(X, 0, 3), 1), -1, Rel.GE, true);
        Proposition two = relation(Map.of(remainder(X, 0, 3), 1), -2, Rel.GE, false);
        DecidingCase.Cases both = new DecidingCase.Cases.One(Proposition.all(List.of(one, two)));
        DecidingCase.Cases either = new DecidingCase.Cases.One(Proposition.any(List.of(one, two)));

        assertFalse(someCaseCrosses(line, both, everyInput()), "x mod 3 is 1 and no more");
        assertTrue(proves(line, both));
        assertTrue(someCaseCrosses(line, either, everyInput()), "x mod 3 is below 2 or at least 1, which is any");
        assertFalse(proves(line, either));
    }
}
