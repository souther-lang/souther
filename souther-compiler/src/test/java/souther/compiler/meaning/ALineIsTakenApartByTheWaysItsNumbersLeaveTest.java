package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line is taken apart where the ways of choosing its cases that no comparison chosen leaves a
 * form no value of are no more than are taken apart, however many the choices multiply to; and the
 * walk that takes it apart asks no way the numbers refute, so it does no more than that count says.
 *
 * <p>Asked with the answer for each condition written here, as
 * {@code WhereALineDecidesIsAskedOfEachCaseItWasSaidForTest} asks it. Whether each condition asked
 * holds some value is asked of the condition itself, by trying values of the number, and not by
 * the intervals the walk reads it with.
 */
class ALineIsTakenApartByTheWaysItsNumbersLeaveTest {

    private static final Proposition SAID = new Proposition.Truth(
            new DecisionSubject.AnInput(TermPath.of("said")), true);

    private static final int TAKEN_APART =
            CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum();

    /** How many rising bounds of one number are chosen among: their choices multiply past what
     *  is taken apart, and they leave a way for each stretch between them. */
    private static final int BOUNDS = 20;

    private static Quantity number(String name) {
        return new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of(name)));
    }

    private static final Quantity X = number("x");

    /** {@code of} at or above {@code at}. */
    private static Proposition atLeast(Quantity of, int at) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(new LinearForm<>(ExactRatio.of(-at),
                new LinkedHashMap<>(Map.of(of, ExactRatio.ONE))), Rel.GE);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }

    /** Whether {@code of} is at or above {@code at}, chosen either way. */
    private static DecidingCase.Cases eitherSideOf(Quantity of, int at) {
        Proposition above = atLeast(of, at);
        return new DecidingCase.Cases.EachOf(List.of(new DecidingCase.Cases.One(above),
                new DecidingCase.Cases.One(above.denied())));
    }

    /** {@code bounds} rising bounds of {@code of}, each chosen either way. */
    private static List<DecidingCase.Cases> risingBounds(Quantity of, int bounds) {
        List<DecidingCase.Cases> out = new ArrayList<>();
        for (int at = 0; at < bounds; at++) {
            out.add(eitherSideOf(of, at * 10));
        }
        return out;
    }

    /** Asks, answering each condition by {@code crossing} and keeping what was asked. */
    private record Asking(Function<Proposition, CasesOfALineAsked.Crossing> crossing,
                          List<Proposition> asked) {

        Asking(Function<Proposition, CasesOfALineAsked.Crossing> crossing) {
            this(crossing, new ArrayList<>());
        }

        CasesOfALineAsked.Found found(DecidingCase.Cases cases) {
            return CasesOfALineAsked.casesOf(new DecidingCase(SAID, cases), condition -> {
                asked.add(condition);
                return crossing.apply(condition);
            });
        }
    }

    /** The comparisons {@code condition} states together; truths beside them are left out. */
    private static List<Proposition.Compared> comparisonsIn(Proposition condition) {
        List<Proposition.Compared> out = new ArrayList<>();
        for (Proposition part : condition instanceof Proposition.All all ? all.parts()
                : List.of(condition)) {
            if (part instanceof Proposition.Compared compared) {
                out.add(compared);
            }
        }
        return out;
    }

    /** Whether some value of the number meets every comparison of {@code condition}, tried
     *  below, at and between every bound, and past the last. */
    private static boolean someValueMeets(Proposition condition) {
        for (int x = -5; x <= BOUNDS * 10; x += 5) {
            ExactRatio value = ExactRatio.of(x);
            if (comparisonsIn(condition).stream().allMatch(each -> holdsAt(each, value))) {
                return true;
            }
        }
        return false;
    }

    private static boolean holdsAt(Proposition.Compared comparison, ExactRatio x) {
        Relation.Affine affine = (Relation.Affine) comparison.relation();
        ExactRatio left = x.times(affine.form().coefs().get(X)).orNull()
                .plus(affine.form().constant()).orNull();
        return affine.proposition().holds(left.signum()) == comparison.holds();
    }

    /**
     * Rising bounds of one number multiply to two to the power of their number, and leave one more
     * way than there are bounds: the line is taken apart, every case of it divides rows, and so it
     * is the case it was said as. Of the prefixes asked, none is one the number has no value in,
     * and they are as many as the consistent prefixes of each depth: the one before the choice and
     * the one past it for the stretch the choice splits, one for each other stretch.
     */
    @Test
    void manyRisingBoundsOfOneNumberAreTakenApart() {
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(risingBounds(X, BOUNDS));
        assertTrue(cases.waysOfChoosing(TAKEN_APART) > TAKEN_APART,
                "more ways as the choices stand than are taken apart");
        Asking asking = new Asking(_ -> CasesOfALineAsked.Crossing.MAY_CROSS);

        CasesOfALineAsked.Found found = asking.found(cases);
        assertEquals(List.of(new DecidingCase(SAID, cases)), found.decidesIn(),
                "every case divides rows, and the line decides in the case as it was said");
        assertEquals(Set.of(), found.notWorkedOut(), "every case worked out");

        List<Proposition> prefixes = asking.asked().subList(1, asking.asked().size());
        assertEquals(List.of(), prefixes.stream().filter(each -> !someValueMeets(each)).toList(),
                "no prefix the number has no value in is asked");
        assertEquals(prefixes.size(), new HashSet<>(prefixes).size(), "and none twice");
        int consistent = 0;
        for (int depth = 0; depth < BOUNDS; depth++) {
            consistent += depth + 2;
        }
        assertEquals(consistent, prefixes.size(),
                "as many as the stretches left at each depth, and one more for the stretch split");
    }

    /**
     * The control: one bound on each of as many numbers as take the ways past what is taken apart.
     * No number refutes a way of another, so every way is consistent and the line is cut off as it
     * was, its count said beside the figure.
     */
    @Test
    void boundsOfIndependentNumbersStayCutOff() {
        int numbers = Integer.SIZE - Integer.numberOfLeadingZeros(TAKEN_APART);
        List<DecidingCase.Cases> choices = new ArrayList<>();
        for (int at = 0; at < numbers; at++) {
            choices.add(eitherSideOf(number("n" + at), 0));
        }
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(choices);
        Asking asking = new Asking(_ -> CasesOfALineAsked.Crossing.MAY_CROSS);

        BigInteger ways = BigInteger.TWO.pow(numbers);
        assertTrue(ways.compareTo(BigInteger.valueOf(TAKEN_APART)) > 0);
        assertEquals(List.of(new CasesOfALineAsked.NotWorkedOut(new DecidingCase(SAID, cases),
                        Set.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO),
                        Optional.of(new CaseCount(new CaseCount.Ways.Exactly(ways),
                                new NumericallyConsistentWays.Counted.AtMost(ways))))),
                asking.found(cases).notWorkedOutIn(), "every way consistent, and none chosen");
        assertEquals(List.of(SAID), asking.asked(), "asked only as it was said");
    }

    /**
     * Remainders of one number moved apart leave few ways, and the intervals leave every one: each
     * remainder is a form of its own there. A line is let in by the intervals, so it is cut off as
     * it stands, and the count a reader is told beside it is the numbers', remainders and all.
     */
    @Test
    void waysOnlyTheRemaindersLeaveFewStayCutOff() {
        int divisor = 7;
        int moved = Integer.SIZE - Integer.numberOfLeadingZeros(TAKEN_APART);
        List<DecidingCase.Cases> choices = new ArrayList<>();
        for (int by = 0; by < moved; by++) {
            Quantity remainder = new Quantity.RemainderOfADividend(
                    ValueName.Stdlib.operation("Int", "floorMod"),
                    new LinearForm<>(ExactRatio.of(by), Map.of(X, ExactRatio.ONE)),
                    BigInteger.valueOf(divisor));
            Relation.OneWay<Quantity> one = Relation.OneWay.of(new LinearForm<>(ExactRatio.ZERO,
                    new LinkedHashMap<>(Map.of(remainder, ExactRatio.ONE))), Rel.EQ);
            Proposition nought = new Proposition.Compared(
                    new Relation.Affine(one.form(), one.proposition()), one.holds());
            choices.add(new DecidingCase.Cases.EachOf(List.of(new DecidingCase.Cases.One(nought),
                    new DecidingCase.Cases.One(nought.denied()))));
        }
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(choices);
        NumericallyConsistentWays.Counts counted = NumericallyConsistentWays.counted(cases);
        BigInteger ways = BigInteger.TWO.pow(moved);
        assertEquals(new NumericallyConsistentWays.Counts(
                        new NumericallyConsistentWays.Counted.AtMost(ways),
                        new NumericallyConsistentWays.Counted.AtMost(BigInteger.valueOf(divisor))),
                counted, "the intervals leave every way, the remainders one for each remainder");
        Asking asking = new Asking(_ -> CasesOfALineAsked.Crossing.MAY_CROSS);

        assertEquals(List.of(new CasesOfALineAsked.NotWorkedOut(new DecidingCase(SAID, cases),
                        Set.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO),
                        Optional.of(new CaseCount(new CaseCount.Ways.Exactly(ways),
                                counted.ofTheNumbers())))),
                asking.found(cases).notWorkedOutIn(), "cut off, told the numbers' count");
        assertEquals(List.of(SAID), asking.asked(), "asked only as it was said");
    }

    /**
     * Two ways that leave the number alike are two cases still: a truth chosen beside the bounds is
     * a choice of its own, and a case is kept or left by its own answer. Here the cases with
     * {@code b}, chosen to the end, hold rows on one side, and every case with {@code a} is kept,
     * each by itself.
     */
    @Test
    void waysLeavingTheNumbersAlikeAreAskedEachAsTheCaseItIs() {
        Proposition a = new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("a")), true);
        Proposition b = new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("b")), true);
        int bounds = 12;
        List<DecidingCase.Cases> choices = new ArrayList<>(List.of(new DecidingCase.Cases.EachOf(
                List.of(new DecidingCase.Cases.One(a), new DecidingCase.Cases.One(b)))));
        choices.addAll(risingBounds(X, bounds));
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(choices);
        assertTrue(cases.waysOfChoosing(TAKEN_APART) > TAKEN_APART);
        // Shown only of the case chosen to the end, so the ways with b are walked as far as the
        // ways with a are, through the same numbers.
        Asking asking = new Asking(condition -> condition instanceof Proposition.All all
                && all.parts().contains(b) && comparisonsIn(condition).size() == bounds
                ? CasesOfALineAsked.Crossing.CANNOT_CROSS : CasesOfALineAsked.Crossing.MAY_CROSS);

        CasesOfALineAsked.Found found = asking.found(cases);
        assertEquals(Set.of(), found.notWorkedOut());
        assertEquals(bounds + 1, found.decidesIn().size(),
                () -> "a case with a for each stretch: " + found.decidesIn());
        assertTrue(found.decidesIn().stream().allMatch(each -> each.condition()
                instanceof Proposition.All all && all.parts().contains(a)
                && someValueMeets(each.condition())), () -> "each with a: " + found.decidesIn());
    }
}
