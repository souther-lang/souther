package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a line is proved to decide in none of the cases it is said for, no two inputs of a small
 * domain, one holding the line and one failing it, meet the same case: tried by every pair of
 * inputs, over cases made by chance of numbers, remainders of numbers, and an element of a set
 * met by {@code some}.
 *
 * <p>The domain is small enough to be tried whole, so what is asked of the proof here is that it
 * never says "none" where a pair is found. That it says "none" at all is asked of the cases that
 * need it: a line at a remainder the cases fix to one side.
 */
class NoCaseCrossesProvesNoneWhereAPairOfRowsMeetsOneCaseTest {

    private static final Quantity X = new DecisionAtom.OfTheInput(
            new NumericTerm.ValueOf(TermPath.of("x")));
    private static final Quantity Y = new DecisionAtom.OfTheInput(
            new NumericTerm.ValueOf(TermPath.of("y")));

    private static final DecisionSubject.AnInput HOLIDAYS =
            new DecisionSubject.AnInput(TermPath.of("holidays"));
    private static final Quantity MEMBER = new DecisionAtom.OfTheInput(
            new NumericTerm.ValueOf(TermPath.of("holidays").element()));

    /** The numbers an input holds are these, and a set holds some of these. */
    private static final int LOW = -2;
    private static final int HIGH = 4;

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

    /** What an input is: two numbers and a set. */
    private record Input(int x, int y, Set<Integer> holidays) {}

    private static List<Input> everyInput() {
        List<Input> out = new ArrayList<>();
        for (int x = LOW; x <= HIGH; x++) {
            for (int y = LOW; y <= HIGH; y++) {
                for (int mask = 0; mask < 8; mask++) {
                    Set<Integer> held = new TreeSet<>();
                    for (int bit = 0; bit < 3; bit++) {
                        if ((mask & (1 << bit)) != 0) {
                            held.add(bit + 1);
                        }
                    }
                    out.add(new Input(x, y, held));
                }
            }
        }
        return out;
    }

    // ---- what a condition holds of an input, worked out here and not by the proof ----

    private static long value(Quantity quantity, Input in, Integer element) {
        if (quantity.equals(X)) {
            return in.x();
        }
        if (quantity.equals(Y)) {
            return in.y();
        }
        if (quantity.equals(MEMBER)) {
            return element;
        }
        Quantity.RemainderOfADividend remainder = (Quantity.RemainderOfADividend) quantity;
        long dividend = form(remainder.dividend(), in, element);
        return Math.floorMod(dividend, remainder.divisor().longValueExact());
    }

    private static long form(LinearForm<Quantity> form, Input in, Integer element) {
        long sum = whole(form.constant());
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            sum += whole(each.getValue()) * value(each.getKey(), in, element);
        }
        return sum;
    }

    private static long whole(ExactRatio ratio) {
        return ((ExactAnswer.Held<BigInteger>) ratio.floor()).value().longValueExact();
    }

    private static boolean holds(Proposition p, Input in, Integer element) {
        return switch (p) {
            case Proposition.Compared c -> {
                Relation.Affine affine = (Relation.Affine) c.relation();
                long form = form(affine.form(), in, element);
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
            case Proposition.All all -> all.parts().stream().allMatch(part -> holds(part, in, element));
            case Proposition.Any any -> any.parts().stream().anyMatch(part -> holds(part, in, element));
            case Proposition.Some some -> {
                boolean found = false;
                for (int each : in.holidays()) {
                    found |= holds(some.ofTheElement(), in, each);
                }
                yield some.holds() == found;
            }
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
            case DecidingCase.Cases.One c -> holds(c.condition(), one, null)
                    && holds(c.condition(), other, null);
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
            if (!holds(line, holding, null)) {
                continue;
            }
            for (Input failing : inputs) {
                if (holds(line, failing, null)) {
                    continue;
                }
                if (someCaseHoldsFor(cases, holding, failing, new IdentityHashMap<>())) {
                    return true;
                }
            }
        }
        return false;
    }

    // ---- cases made by chance ----

    /** Every remainder here is of {@code x} by 3 unless a round says otherwise, so that what a
     *  case says of one is read against the line. */
    private static Proposition atom(Random chance) {
        return switch (chance.nextInt(6)) {
            case 0 -> relation(Map.of(X, 1), -chance.nextInt(HIGH), Rel.GE, chance.nextBoolean());
            case 1 -> relation(Map.of(X, 1, Y, -1), chance.nextInt(5) - 2, Rel.GE,
                    chance.nextBoolean());
            case 2, 3 -> relation(Map.of(remainder(X, chance.nextInt(5) - 1, 3), 1),
                    -chance.nextInt(3), chance.nextBoolean() ? Rel.GE : Rel.EQ,
                    chance.nextBoolean());
            case 4 -> relation(Map.of(remainder(Y, chance.nextInt(3), 3), 1), -chance.nextInt(2),
                    Rel.EQ, chance.nextBoolean());
            default -> new Proposition.Some(HOLIDAYS, relation(Map.of(MEMBER, 1, X, -1),
                    chance.nextInt(3) - 1, Rel.EQ, true), chance.nextBoolean());
        };
    }

    private static DecidingCase.Cases cases(Random chance, int depth,
                                            List<DecidingCase.Cases> shareable) {
        if (!shareable.isEmpty() && chance.nextInt(5) == 0) {
            return shareable.get(chance.nextInt(shareable.size()));
        }
        DecidingCase.Cases made;
        if (depth == 0 || chance.nextInt(3) == 0) {
            Proposition condition = chance.nextInt(6) == 0
                    ? Proposition.all(List.of(atom(chance), atom(chance)))
                    : chance.nextInt(8) == 0
                    ? Proposition.any(List.of(atom(chance), atom(chance)))
                    : atom(chance);
            made = new DecidingCase.Cases.One(condition);
        } else if (chance.nextBoolean()) {
            List<DecidingCase.Cases> alternatives = new ArrayList<>();
            for (int i = 0; i < 2 + chance.nextInt(2); i++) {
                alternatives.add(cases(chance, depth - 1, shareable));
            }
            made = new DecidingCase.Cases.EachOf(alternatives);
        } else {
            List<DecidingCase.Cases> factors = new ArrayList<>();
            for (int i = 0; i < 2 + chance.nextInt(2); i++) {
                factors.add(cases(chance, depth - 1, shareable));
            }
            made = DecidingCase.Cases.together(factors);
        }
        shareable.add(made);
        return made;
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
        DecidingCase.Cases cases = DecidingCase.Cases.together(List.of(
                new DecidingCase.Cases.One(relation(Map.of(remainder(X, 1, 3), 1), 0, Rel.EQ, true)),
                new DecidingCase.Cases.NotTakenApart(
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.atDeclared())));

        assertFalse(proves(line, cases) && someCaseCrosses(line, cases, everyInput()));
    }

    @Test
    void aProofNeverLeavesOutAPairOfInputsMeetingOneCase() {
        List<Input> inputs = everyInput();
        Random chance = new Random(20240611);
        int proved = 0;
        int tried = 0;
        for (int round = 0; round < 150; round++) {
            DecidingCase.Cases cases = cases(chance, 3, new ArrayList<>());
            Proposition.Compared line = remainderLine(chance.nextInt(3), chance.nextInt(3));
            tried++;
            if (proves(line, cases)) {
                proved++;
                assertFalse(someCaseCrosses(line, cases, inputs),
                        "proved that no case crosses " + line + ", and two inputs meet one case: "
                                + cases);
            }
        }
        assertTrue(proved > 0 && proved < tried,
                "a proof is made for some of the cases and not for all: " + proved + " of " + tried);
    }
}
