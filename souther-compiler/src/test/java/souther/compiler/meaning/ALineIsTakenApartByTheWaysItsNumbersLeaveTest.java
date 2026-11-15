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
     * and they are only those the walk goes on more than one way past, or ends at: below a bound
     * the number is decided at every bound after it, so that way is asked once, at its end.
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
        assertEquals(2 * BOUNDS, prefixes.size(),
                "for each bound, the way below it, which the number leaves one way on past it and"
                        + " is asked at its end, and the prefix above it, asked before the next"
                        + " bound splits the number again or at the end past the last");
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
                        Set.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.reached()),
                        Optional.of(new CaseCount(new CaseCount.Ways.Exactly(ways),
                                new NumericallyConsistentWays.Counted.AtMost(ways))))),
                asking.found(cases).notWorkedOutIn(), "every way consistent, and none chosen");
        assertEquals(List.of(SAID), asking.asked(), "asked only as it was said");
    }

    /** {@code floorMod(of + by, divisor) == 0}. */
    private static Proposition noughtLeft(Quantity of, int by, int divisor) {
        Quantity remainder = new Quantity.RemainderOfADividend(
                ValueName.Stdlib.operation("Int", "floorMod"),
                new LinearForm<>(ExactRatio.of(by), Map.of(of, ExactRatio.ONE)),
                BigInteger.valueOf(divisor));
        Relation.OneWay<Quantity> one = Relation.OneWay.of(new LinearForm<>(ExactRatio.ZERO,
                new LinkedHashMap<>(Map.of(remainder, ExactRatio.ONE))), Rel.EQ);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }

    /** Whether {@code of} moved by each of {@code moved} leaves nothing over {@code divisor},
     *  chosen either way for each. */
    private static List<DecidingCase.Cases> remaindersMovedApart(Quantity of, int moved,
                                                                 int divisor) {
        List<DecidingCase.Cases> out = new ArrayList<>();
        for (int by = 0; by < moved; by++) {
            Proposition nought = noughtLeft(of, by, divisor);
            out.add(new DecidingCase.Cases.EachOf(List.of(new DecidingCase.Cases.One(nought),
                    new DecidingCase.Cases.One(nought.denied()))));
        }
        return out;
    }

    /** Whether some remainder of {@code x} by {@code divisor} meets every comparison of a
     *  remainder of {@code x} moved that {@code condition} states, tried at each. */
    private static boolean someRemainderMeets(Proposition condition, int divisor) {
        for (int x = 0; x < divisor; x++) {
            int at = x;
            if (comparisonsIn(condition).stream().allMatch(each -> {
                Relation.Affine affine = (Relation.Affine) each.relation();
                Quantity.RemainderOfADividend remainder = (Quantity.RemainderOfADividend)
                        affine.form().coefs().keySet().iterator().next();
                int moved = remainder.dividend().constant().floor().orNull().intValueExact();
                boolean nought = Math.floorMod(at + moved, divisor) == 0;
                return (nought == (affine.proposition() == Rel.EQ)) == each.holds();
            })) {
                return true;
            }
        }
        return false;
    }

    /**
     * Remainders of one number moved apart leave few ways, and the intervals leave every one: each
     * remainder is a form of its own there. The line is taken apart by the remainders' count, and
     * walked from each remainder, so no prefix asked is one the remainders refute; and since from
     * one remainder every comparison is decided before it is a choice, the walk goes on along one
     * way from each, and asks it once, at its end.
     */
    @Test
    void waysOnlyTheRemaindersLeaveFewAreWalkedFromEachRemainder() {
        int divisor = 7;
        int moved = Integer.SIZE - Integer.numberOfLeadingZeros(TAKEN_APART);
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(
                remaindersMovedApart(X, moved, divisor));
        NumericallyConsistentWays.Counts counted = NumericallyConsistentWays.counted(cases);
        BigInteger ways = BigInteger.TWO.pow(moved);
        assertEquals(new NumericallyConsistentWays.Counts(
                        new NumericallyConsistentWays.Counted.AtMost(ways),
                        new NumericallyConsistentWays.Counted.AtMost(BigInteger.valueOf(divisor))),
                counted, "the intervals leave every way, the remainders one for each remainder");
        Asking asking = new Asking(_ -> CasesOfALineAsked.Crossing.MAY_CROSS);

        CasesOfALineAsked.Found found = asking.found(cases);
        assertEquals(List.of(new DecidingCase(SAID, cases)), found.decidesIn(),
                "every case divides rows, and the line decides in the case as it was said");
        assertEquals(Set.of(), found.notWorkedOut(), "every case worked out");
        List<Proposition> prefixes = asking.asked().subList(1, asking.asked().size());
        assertEquals(List.of(), prefixes.stream()
                        .filter(each -> !someRemainderMeets(each, divisor)).toList(),
                "no prefix the remainders refute is asked");
        assertEquals(divisor, prefixes.size(),
                () -> "one question for each remainder: " + prefixes);
        assertEquals(divisor, new HashSet<>(prefixes).size(), "each of a way of its own");
    }

    /**
     * The control: two dividends compared more than one way each, whose classes of remainders
     * together are more starts than a line is walked from. The remainders leave few ways, and the intervals
     * many; walked from nothing chosen, a prefix would be refuted only late, so the line is cut off
     * as it stands, told the numbers' count.
     */
    @Test
    void remaindersOfTwoDividendsPastTheStartsStayCutOff() {
        int moved = 8;
        List<DecidingCase.Cases> choices = new ArrayList<>(remaindersMovedApart(X, moved, 11));
        choices.addAll(remaindersMovedApart(number("y"), moved, 13));
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(choices);
        assertTrue((moved + 1) * (moved + 1) > NumericallyConsistentWays.MOST_STARTS,
                "more starts than are walked: a class for each moved, and one of the rest");
        assertEquals(Optional.empty(), NumericallyConsistentWays.startingAtEachRemainder(cases));
        NumericallyConsistentWays.Counts counted = NumericallyConsistentWays.counted(cases);
        BigInteger leftEach = BigInteger.valueOf(moved + 1);
        assertEquals(new NumericallyConsistentWays.Counted.AtMost(leftEach.multiply(leftEach)),
                counted.ofTheNumbers(), "one zero among the moved, or none, for each dividend");
        Asking asking = new Asking(_ -> CasesOfALineAsked.Crossing.MAY_CROSS);

        BigInteger ways = BigInteger.TWO.pow(2 * moved);
        assertEquals(List.of(new CasesOfALineAsked.NotWorkedOut(new DecidingCase(SAID, cases),
                        Set.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.reached()),
                        Optional.of(new CaseCount(new CaseCount.Ways.Exactly(ways),
                                counted.ofTheNumbers())))),
                asking.found(cases).notWorkedOutIn(), "cut off, told the numbers' count");
        assertEquals(List.of(SAID), asking.asked(), "asked only as it was said");
    }

    /**
     * A way that holds at more than one remainder is walked from each, and is still one case.
     * Moved by fewer than the divisor, every comparison left non-zero holds at three remainders of
     * thirteen; that way is shown to hold rows on one side only, so the line is read in the others,
     * each by itself and none twice.
     */
    @Test
    void aWayHoldingAtSeveralRemaindersIsOneCase() {
        int divisor = 13;
        int moved = Integer.SIZE - Integer.numberOfLeadingZeros(TAKEN_APART);
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(
                remaindersMovedApart(X, moved, divisor));
        assertEquals(new NumericallyConsistentWays.Counted.AtMost(BigInteger.valueOf(moved + 1)),
                NumericallyConsistentWays.counted(cases).ofTheNumbers(),
                "one zero among the moved, or none");
        Asking asking = new Asking(condition -> comparisonsIn(condition).size() == moved
                && comparisonsIn(condition).stream().noneMatch(Proposition.Compared::holds)
                ? CasesOfALineAsked.Crossing.CANNOT_CROSS : CasesOfALineAsked.Crossing.MAY_CROSS);

        CasesOfALineAsked.Found found = asking.found(cases);
        assertEquals(Set.of(), found.notWorkedOut());
        assertEquals(moved, found.decidesIn().size(),
                () -> "a case for each comparison left nought: " + found.decidesIn());
        assertTrue(found.decidesIn().stream().allMatch(each ->
                        comparisonsIn(each.condition()).stream()
                                .filter(Proposition.Compared::holds).count() == 1),
                () -> "each with one nought: " + found.decidesIn());
    }

    /**
     * Remainders no comparison tells apart are one start: moved by 0, 1 and 2, the comparisons of a
     * remainder by seven leave four classes of remainder, those that are nought at one of them and
     * the four that are nought at none.
     */
    @Test
    void remaindersNoComparisonTellsApartAreOneStart() {
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(
                remaindersMovedApart(X, 3, 7));
        List<NumericallyConsistentWays.State> starts =
                NumericallyConsistentWays.startingAtEachRemainder(cases).orElseThrow().states();
        assertEquals(4, starts.size(), () -> "one start for each class: " + starts);
    }

    /**
     * Two dividends, each compared more than one way, are walked from each pair of what tells their
     * remainders apart: three classes of one by three, five of the other by five, fifteen starts.
     */
    @Test
    void remaindersOfTwoDividendsAreWalkedFromEachPairOfClasses() {
        List<DecidingCase.Cases> choices = new ArrayList<>(remaindersMovedApart(X, 3, 3));
        choices.addAll(remaindersMovedApart(number("y"), 5, 5));
        List<NumericallyConsistentWays.State> starts = NumericallyConsistentWays
                .startingAtEachRemainder(new DecidingCase.Cases.Together(choices)).orElseThrow()
                .states();
        assertEquals(15, starts.size(), () -> "three by five: " + starts);
    }

    /**
     * The ways walked are counted as they are walked. Seven comparisons of a remainder by seven,
     * each chosen or a truth beside it taken instead, leave eight ways, those that take none of the
     * comparisons holding at every remainder: with six truths beside them that is 512 ways the
     * numbers leave, within what is taken apart, and 896 walked from the seven starts. The line is
     * cut off and told the numbers' count, and no prefix is asked.
     */
    @Test
    void waysHoldingAtSeveralStartsAreCountedAsManyTimesAsTheyAreWalked() {
        List<DecidingCase.Cases> choices = new ArrayList<>();
        for (int by = 0; by < 7; by++) {
            Proposition truth = new Proposition.Truth(
                    new DecisionSubject.AnInput(TermPath.of("skipped" + by)), true);
            choices.add(new DecidingCase.Cases.EachOf(List.of(
                    new DecidingCase.Cases.One(noughtLeft(X, by, 7)),
                    new DecidingCase.Cases.One(truth))));
        }
        for (int at = 0; at < 6; at++) {
            Proposition truth = new Proposition.Truth(
                    new DecisionSubject.AnInput(TermPath.of("t" + at)), true);
            choices.add(new DecidingCase.Cases.EachOf(List.of(new DecidingCase.Cases.One(truth),
                    new DecidingCase.Cases.One(truth.denied()))));
        }
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(choices);
        NumericallyConsistentWays.Counts counted = NumericallyConsistentWays.counted(cases);
        assertEquals(new NumericallyConsistentWays.Counted.AtMost(BigInteger.valueOf(8L << 6)),
                counted.ofTheNumbers(), "eight ways, each times 64");
        assertEquals(BigInteger.valueOf(14L << 6), NumericallyConsistentWays
                        .startingAtEachRemainder(cases).orElseThrow().walked(),
                "the one that takes none walked from each of seven, the seven from one");
        Asking asking = new Asking(_ -> CasesOfALineAsked.Crossing.MAY_CROSS);

        assertEquals(List.of(new CasesOfALineAsked.NotWorkedOut(new DecidingCase(SAID, cases),
                        Set.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.reached()),
                        Optional.of(new CaseCount(
                                new CaseCount.Ways.Exactly(BigInteger.TWO.pow(13)),
                                counted.ofTheNumbers())))),
                asking.found(cases).notWorkedOutIn(), "cut off, told the numbers' count");
        assertEquals(List.of(SAID), asking.asked(), "asked only as it was said");
    }

    /**
     * Remainders no comparison tells apart are walked once. Three comparisons of a remainder by
     * seven, moved by 0, 1 and 2, leave four ways, and seven choices of truths beside them multiply
     * each by 128. The line is read in 512 cases and no way is asked twice: from the four remainders
     * that are nought at none the walk is the same, so they are one start.
     */
    @Test
    void remaindersNoComparisonTellsApartAreNotWalkedMoreThanOnce() {
        List<DecidingCase.Cases> choices = new ArrayList<>(remaindersMovedApart(X, 3, 7));
        int truths = 7;
        for (int at = 0; at < truths; at++) {
            Proposition truth = new Proposition.Truth(
                    new DecisionSubject.AnInput(TermPath.of("t" + at)), true);
            choices.add(new DecidingCase.Cases.EachOf(List.of(new DecidingCase.Cases.One(truth),
                    new DecidingCase.Cases.One(truth.denied()))));
        }
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(choices);
        assertEquals(new NumericallyConsistentWays.Counted.AtMost(
                        BigInteger.valueOf(4L << truths)),
                NumericallyConsistentWays.counted(cases).ofTheNumbers(), "four ways, each times 128");
        Asking asking = new Asking(_ -> CasesOfALineAsked.Crossing.MAY_CROSS);

        CasesOfALineAsked.Found found = asking.found(cases);
        assertEquals(Set.of(), found.notWorkedOut(), "every case worked out");
        assertEquals(new HashSet<>(asking.asked()).size(), asking.asked().size(),
                "no condition asked twice");
    }

    /**
     * A prefix whose question was put off, since the walk went on along one way past it, is still
     * asked before anything is said of the cases past it: where no row is in it, the cases nobody
     * took apart past it are no cases of the line, and no figure is said for them.
     */
    @Test
    void aPrefixWhoseQuestionWasPutOffSaysNothingOfCasesPastItWhereNoRowIsInIt() {
        Proposition none = new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("none")),
                true);
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(List.of(
                new DecidingCase.Cases.One(none),
                new DecidingCase.Cases.EachOf(List.of(new DecidingCase.Cases.NotTakenApart(
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.reached())))));
        Asking asking = new Asking(condition -> condition.equals(none)
                ? CasesOfALineAsked.Crossing.NO_ROWS : CasesOfALineAsked.Crossing.MAY_CROSS);

        CasesOfALineAsked.Found found = asking.found(cases);
        assertEquals(List.of(), found.decidesIn(), "no case");
        assertEquals(Set.of(), found.notWorkedOut(), "and nothing said of the cases past it");
        assertTrue(asking.asked().contains(none), "asked once the walk came to them");
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
