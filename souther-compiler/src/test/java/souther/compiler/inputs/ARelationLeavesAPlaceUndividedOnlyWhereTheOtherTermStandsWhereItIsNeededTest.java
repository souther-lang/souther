package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which places a relation of terms is shown to leave undivided, asked of the terms themselves.
 *
 * <p>Each case is a pair: the relation as it stands, which some value of a place settles whatever
 * the rest hold, and the one change that takes that value away. A judgment that let the first
 * through, or held back the second, would not be telling the two apart.
 */
class ARelationLeavesAPlaceUndividedOnlyWhereTheOtherTermStandsWhereItIsNeededTest {

    private static final Object A_DATE = "Date";

    private static NumericDomain.Bounds run(long low, long high) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(low)),
                Endpoint.inclusive(Count.of(high)));
    }

    /** Where the order every term here is counted on stops, unless a case says otherwise: an
     *  {@code Int}'s. */
    private static final NumericDomain.Bounds INTS = run(Long.MIN_VALUE, Long.MAX_VALUE);

    /** The greatest {@code Int}, which the form is worked out in. */
    private static final BigInteger GREATEST_INT = BigInteger.valueOf(Long.MAX_VALUE);

    /** Where a date's order stops, as days. */
    private static final NumericDomain.Bounds DAYS =
            run(LocalDate.MIN.toEpochDay(), LocalDate.MAX.toEpochDay());

    private static WhatARelationLeavesUndivided.Term<String> term(String place, long weight,
                                                                 NumericDomain.Bounds holds,
                                                                 NumericDomain.Bounds realizes,
                                                                 Object takes, boolean itsPlace) {
        return runningTo(INTS, place, weight, holds, realizes, takes, itsPlace);
    }

    private static WhatARelationLeavesUndivided.Term<String> runningTo(
            NumericDomain.Bounds stops, String place, long weight, NumericDomain.Bounds holds,
            NumericDomain.Bounds realizes, Object takes, boolean itsPlace) {
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight), holds,
                realizes, takes, itsPlace, Granularity.DISCRETE, stops);
    }

    private static Set<String> undivided(List<WhatARelationLeavesUndivided.Term<String>> terms,
                                         ExactRatio constant, Rel relation) {
        return WhatARelationLeavesUndivided.of(terms, constant, relation, String::equals,
                (one, other) -> true, GREATEST_INT);
    }

    /**
     * {@code 2x < y}, {@code y} from four to eight: at four it needs an {@code x} below two, and
     * {@code x} from three on is never there, so {@code y} at four makes it false whatever
     * {@code x} is. From one on, {@code x} is below two and at four too.
     */
    @Test
    void aWeighedTermHasToStandAtTheRestOverItsWeight() {
        for (long least : List.of(3L, 1L)) {
            Set<String> left = undivided(List.of(
                            term("x", 2, run(least, 10), run(least, 10), null, true),
                            term("y", -1, run(4, 8), null, null, true)),
                    ExactRatio.ZERO, Rel.LT);
            assertEquals(least == 3 ? Set.of() : Set.of("y"), left, "x from " + least);
        }
    }

    /**
     * {@code Date.daysBetween(a, b) == 1}: at the last date {@code a} needs a {@code b} no date
     * is, so the two taking the same values does not leave it undivided by what the other reaches.
     * Held to be one value, each is the other's. How far apart the two are is the other reading,
     * below.
     */
    @Test
    void twoTermsTakingTheSameValuesLeaveEachOtherUndividedOnlyWhereEachIsTheOthersValue() {
        for (long apart : List.of(1L, 0L)) {
            Set<String> left = undivided(List.of(
                            term("a", -1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                                    A_DATE, true),
                            term("b", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                                    A_DATE, true)),
                    ExactRatio.of(-apart), Rel.EQ);
            assertEquals(apart == 1 ? Set.of() : Set.of("a", "b"), left, "apart by " + apart);
        }
    }

    /** {@code x + 1 < y} over values nothing restricts: the least {@code y} needs an {@code x}
     *  below the least, which no value is, so what the other reaches leaves nothing undivided. */
    @Test
    void anEndOfTheTypeMovedByAConstantIsNeededPastTheEnd() {
        for (long by : List.of(1L, 0L)) {
            Set<String> left = undivided(List.of(
                            term("x", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                                    null, true),
                            term("y", -1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                                    null, true)),
                    ExactRatio.of(by), Rel.LT);
            assertEquals(by == 1 ? Set.of() : Set.of("x", "y"), left, "moved by " + by);
        }
    }

    /**
     * {@code d < a}, where {@code a} is what an operation answers and runs to the least value: the
     * values it is answered at there are not one value of its place, and none of them has a
     * {@code d} below. Where {@code a} is the value at its place, the least is that value alone.
     */
    @Test
    void anEndAnAnswerRunsToIsNotTheEndOfItsPlace() {
        for (boolean itsPlace : List.of(false, true)) {
            Set<String> left = undivided(List.of(
                            term("d", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                                    null, true),
                            term("s", -1, NumericDomain.Bounds.OPEN, null, null, itsPlace)),
                    ExactRatio.ZERO, Rel.LT);
            assertEquals(itsPlace ? Set.of("s") : Set.of(), left, "its place: " + itsPlace);
        }
    }

    /**
     * {@code d < n}, a day count against an {@code Int}: each stands at the other's value, and
     * every day has an {@code Int} on each side, but an {@code Int} past the last day has no day
     * above it. So {@code n} is reached only by a term that runs on as far as an {@code Int}.
     */
    @Test
    void aTermStandingAtTheOthersValueReachesItOnlyAsFarAsItsOwnOrderRuns() {
        for (NumericDomain.Bounds dayStops : List.of(DAYS, INTS)) {
            Set<String> left = undivided(List.of(
                            runningTo(dayStops, "d", 1, NumericDomain.Bounds.OPEN,
                                    NumericDomain.Bounds.OPEN, null, true),
                            term("n", -1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                                    null, true)),
                    ExactRatio.ZERO, Rel.LT);
            assertEquals(dayStops == DAYS ? Set.of("d") : Set.of("d", "n"), left,
                    "the day stopping at " + dayStops);
        }
    }

    /** {@code d - r + w >= 0}, two dates and an {@code Int} taking {@code w}, each the value at its
     *  place and every value of its type. */
    private static List<WhatARelationLeavesUndivided.Term<String>> aWindow(NumericDomain.Bounds w) {
        return List.of(
                runningTo(DAYS, "d", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                        A_DATE, true),
                runningTo(DAYS, "r", -1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                        A_DATE, true),
                term("w", 1, NumericDomain.Bounds.OPEN, w, null, true));
    }

    /**
     * {@code d - r + w >= 0}: with {@code w} held at nought the two dates are held against each
     * other alone, and each reaches every value of the other. {@code w} is reached by neither:
     * past the farthest two dates are apart, a count of days settles it. Held still, {@code w} has
     * to be shown to take nought, and a {@code w} shown to take nothing holds the dates at nothing.
     */
    @Test
    void aThirdTermHeldStillLeavesTwoTermsHeldAgainstEachOther() {
        assertEquals(Set.of("d", "r"),
                undivided(aWindow(NumericDomain.Bounds.OPEN), ExactRatio.ZERO, Rel.GE));
        assertEquals(Set.of(), undivided(aWindow(run(1, 0)), ExactRatio.ZERO, Rel.GE));
    }

    /**
     * The same relation, asked of {@code w}: every value up to the farthest two dates are apart is
     * reached by choosing both dates, and past it the type's lines alone settle it, so {@code w}
     * is left undivided. A date whose order is read as running on takes the days there are.
     */
    @Test
    void twoDatesTogetherReachTheValuesOfACountOfDays() {
        var leaves = WhatARelationLeavesUndivided.leavesOf(aWindow(NumericDomain.Bounds.OPEN), 2,
                ExactRatio.ZERO, Rel.GE, String::equals, (one, other) -> true,
                Granularity.DISCRETE, GREATEST_INT);

        var settled = assertInstanceOf(WhatARelationLeavesUndivided.Leaves.Settled.class, leaves);
        assertFalse(settled.ofTheTypeAlone().isEmpty());
        assertTrue(settled.linesOfTheModel().isEmpty());
    }

    /** The same, with {@code w} tied to {@code d}: holding it still may hold {@code d} too. */
    @Test
    void aThirdTermTiedToOneOfThemIsNotHeldStill() {
        Set<String> left = WhatARelationLeavesUndivided.of(aWindow(NumericDomain.Bounds.OPEN),
                ExactRatio.ZERO, Rel.GE, String::equals,
                (one, other) -> !Set.of(one, other).equals(Set.of(0, 2)), GREATEST_INT);
        assertEquals(Set.of(), left);
    }

    private static WhatARelationLeavesUndivided.Term<String> decimal(
            String place, long weight, NumericDomain.Bounds realizes,
            NumericDomain.Bounds stops) {
        NumericDomain.Bounds atNoughtOrMore =
                new NumericDomain.Bounds(Endpoint.inclusive(Count.ZERO), null);
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight),
                atNoughtOrMore, realizes, null, true, Granularity.DENSE, stops);
    }

    /**
     * {@code n + t - g + s <= 0}, each at nought or more and {@code s} shown to take nothing. A
     * {@code g} far enough up holds it wherever the rest stand and a {@code t} far enough up fails
     * it, since a decimal runs on without end, so {@code n}, {@code t} and {@code s} are each left
     * either way. {@code g} is not: nothing shown to run on takes the sum up past it while
     * {@code s} may stand anywhere. With {@code t} counted on an {@code Int}'s order, it runs out,
     * and nothing takes the sum up past an {@code n} beyond the greatest {@code Int}; {@code t}
     * itself is still taken past by {@code n}.
     */
    @Test
    void aDecimalRunningOnWithoutEndReachesEitherSideOfAnyValue() {
        NumericDomain.Bounds upward = new NumericDomain.Bounds(Endpoint.inclusive(Count.ZERO), null);
        for (NumericDomain.Bounds tStops : List.of(NumericDomain.Bounds.OPEN, INTS)) {
            Set<String> left = undivided(List.of(
                            decimal("n", 1, upward, NumericDomain.Bounds.OPEN),
                            decimal("t", 1, upward, tStops),
                            decimal("g", -1, upward, NumericDomain.Bounds.OPEN),
                            decimal("s", 1, null, NumericDomain.Bounds.OPEN)),
                    ExactRatio.ZERO, Rel.LE);
            assertEquals(tStops == INTS ? Set.of("t", "s") : Set.of("n", "t", "s"), left,
                    "t stopping at " + tStops);
        }
    }

    /** Two values at their places, weighed {@code first} and {@code second}, the first a date and
     *  the second taking {@code takes}, each every value of what it takes. */
    private static List<WhatARelationLeavesUndivided.Term<String>> pair(long first, long second,
                                                                       Object takes) {
        return List.of(
                term("a", first, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN, A_DATE,
                        true),
                term("b", second, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN, takes,
                        true));
    }

    private static WhatARelationLeavesUndivided.OnTheDifference held(long weight, long constant,
                                                                     Rel relation) {
        return new WhatARelationLeavesUndivided.OnTheDifference(ExactRatio.of(weight),
                ExactRatio.of(constant), relation);
    }

    /** The days a date can be written on, which is where the type two dates take stops. */
    private static final WhatARelationLeavesUndivided.WhereTheRepresentationStops DATES =
            new WhatARelationLeavesUndivided.WhereTheRepresentationStops(DAYS);

    private static Set<String> apart(List<WhatARelationLeavesUndivided.Term<String>> terms,
                                     long constant, Rel relation,
                                     WhatARelationLeavesUndivided.OnTheDifference... held) {
        return WhatARelationLeavesUndivided.ofTheirDifference(terms, ExactRatio.of(constant),
                relation, List.of(held), DATES, String::equals, GREATEST_INT,
                WhatARelationLeavesUndivided.Operations.NONE, true);
    }

    /**
     * No two dates are ten trillion days apart, so {@code a - b > 10^13} holds for none of them and
     * {@code a} settles it wherever it stands. Fourteen days apart, every date but those beside the
     * two ends has partners on both sides.
     */
    @Test
    void aDifferenceNoTwoValuesAreApartByIsNoOutcome() {
        assertEquals(Set.of(), apart(pair(1, -1, A_DATE), -10_000_000_000_000L, Rel.GT));
        assertEquals(Set.of("a", "b"), apart(pair(1, -1, A_DATE), -14, Rel.GT));
    }

    /**
     * Four hundred billion days is more than half the dates there are: only dates nearer the two
     * ends than the middle is are that far apart, and every other date settles
     * {@code a - b > 4 * 10^11} alone. Three hundred billion is less than half, and the middle date
     * has a partner on either side of it, so the dates settling it alone are those beside an end.
     */
    @Test
    void theMiddleOfTheTypeHasToSeeBothOutcomes() {
        assertEquals(Set.of(), apart(pair(1, -1, A_DATE), -400_000_000_000L, Rel.GT));
        assertEquals(Set.of("a", "b"), apart(pair(1, -1, A_DATE), -300_000_000_000L, Rel.GT));
    }

    /**
     * Read of their difference, {@code a + K > b} over amounts from nought, {@code K} nine
     * quintillion: an {@code a} past the greatest {@code Int} less {@code K} has no row computed,
     * since {@code a + K} is past the type whatever {@code b} is. The answer says so, as a run
     * whose line is the type's alone, and draws no line of the model on {@code a}; on {@code b}
     * it draws the model's line at {@code K}, below which every {@code a} holds it, and the
     * values from the greatest {@code Int} on are the type's alone, since the rows that hold the
     * relation there are the ones no row computes.
     */
    @Test
    void aValueNoRowIsComputedAtIsARunOfTheTypeAloneInTheReadingOfADifference() {
        long k = 9_000_000_000_000_000_000L;
        NumericDomain.Bounds amounts =
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)), null);
        List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                term("a", 1, amounts, amounts, null, true),
                term("b", -1, amounts, amounts, null, true));

        WhatARelationLeavesUndivided.Leaves.Settled a =
                (WhatARelationLeavesUndivided.Leaves.Settled) WhatARelationLeavesUndivided
                        .leavesByTheirDifference(terms, 0, ExactRatio.of(k), Rel.GT, List.of(),
                                String::equals, GREATEST_INT,
                                WhatARelationLeavesUndivided.Operations.NONE, true);
        assertEquals(List.of(), a.linesOfTheModel());
        assertEquals(List.of(new WhatARelationLeavesUndivided.Line(Rel.GE,
                ExactRatio.of(Long.MAX_VALUE - k + 1))), a.ofTheTypeAlone());

        WhatARelationLeavesUndivided.Leaves.Settled b =
                (WhatARelationLeavesUndivided.Leaves.Settled) WhatARelationLeavesUndivided
                        .leavesByTheirDifference(terms, 1, ExactRatio.of(k), Rel.GT, List.of(),
                                String::equals, GREATEST_INT,
                                WhatARelationLeavesUndivided.Operations.NONE, true);
        assertEquals(List.of(new WhatARelationLeavesUndivided.Line(Rel.LE, ExactRatio.of(k - 1))),
                b.linesOfTheModel());
        // At the greatest Int itself {@code a} would have to pass the greatest less K for the
        // relation to hold, and no row computes {@code a + K} there: the rows computed fail it.
        assertEquals(List.of(new WhatARelationLeavesUndivided.Line(Rel.GE,
                ExactRatio.of(Long.MAX_VALUE))), b.ofTheTypeAlone());
    }

    /**
     * The same where {@code a} is what an operation answers and not the value at a place: every
     * row that answers it past the greatest {@code Int} less {@code K} stands there, so those
     * values are no end the type passes over, and nothing is shown.
     */
    @Test
    void aValueNoRowIsComputedAtIsNoRunOfTheTypeWhereItIsNoPlace() {
        long k = 9_000_000_000_000_000_000L;
        NumericDomain.Bounds amounts =
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)), null);
        List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                term("a", 1, amounts, amounts, null, false),
                term("b", -1, amounts, amounts, null, true));

        assertNull(WhatARelationLeavesUndivided.leavesByTheirDifference(terms, 0,
                ExactRatio.of(k), Rel.GT, List.of(), String::equals, GREATEST_INT,
                WhatARelationLeavesUndivided.Operations.NONE, true));
    }

    /**
     * Read of their difference, {@code t > w} where every row holds {@code t >= w}, both from
     * nought: a {@code w} at the greatest {@code Int} has no {@code t} above it, which is where
     * the type stops and no line of the model's. The answer keeps it as the type's line, and
     * draws none of the model's on {@code w}.
     */
    @Test
    void aValueOnlyTheOrdersEndKeepsFromAnOutcomeIsARunOfTheTypeAlone() {
        NumericDomain.Bounds amounts =
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)), null);
        List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                term("t", 1, amounts, amounts, null, true),
                term("w", -1, amounts, amounts, null, true));
        WhatARelationLeavesUndivided.Leaves.Settled w =
                (WhatARelationLeavesUndivided.Leaves.Settled) WhatARelationLeavesUndivided
                        .leavesByTheirDifference(terms, 1, ExactRatio.ZERO, Rel.GT,
                                List.of(new WhatARelationLeavesUndivided.OnTheDifference(
                                        ExactRatio.ONE, ExactRatio.ZERO, Rel.GE)),
                                String::equals, GREATEST_INT,
                                WhatARelationLeavesUndivided.Operations.NONE, true);

        assertEquals(List.of(), w.linesOfTheModel());
        assertEquals(List.of(new WhatARelationLeavesUndivided.Line(Rel.GE,
                ExactRatio.of(Long.MAX_VALUE))), w.ofTheTypeAlone());
    }

    /**
     * Read of their difference, {@code w > t} where every row holds {@code w >= t}, {@code w}
     * from nought to ten and {@code t} from nought: a {@code t} past ten has no {@code w} at all,
     * so no row reaches it on either side, and nothing is shown of {@code t}. Held to ten as well,
     * {@code t} is parted at ten, which no {@code w} is above.
     */
    @Test
    void aValueNoRowOfEitherSideReachesIsNoValueLeftEitherWay() {
        NumericDomain.Bounds amounts =
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)), null);
        List<WhatARelationLeavesUndivided.OnTheDifference> atLeast =
                List.of(new WhatARelationLeavesUndivided.OnTheDifference(ExactRatio.ONE,
                        ExactRatio.ZERO, Rel.GE));
        for (NumericDomain.Bounds held : List.of(amounts, run(0, 10))) {
            List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                    term("w", 1, run(0, 10), run(0, 10), null, true),
                    term("t", -1, held, held, null, true));
            WhatARelationLeavesUndivided.Leaves t = WhatARelationLeavesUndivided
                    .leavesByTheirDifference(terms, 1, ExactRatio.ZERO, Rel.GT, atLeast,
                            String::equals, GREATEST_INT,
                            WhatARelationLeavesUndivided.Operations.NONE, true);
            if (held == amounts) {
                assertNull(t);
            } else {
                assertEquals(List.of(new WhatARelationLeavesUndivided.Line(Rel.GE,
                        ExactRatio.of(10))), ((WhatARelationLeavesUndivided.Leaves.Settled) t)
                        .linesOfTheModel());
            }
        }
    }

    /**
     * {@code a + c - s - 5 >= 0} over decimals, {@code c} above five and below ten: held at a
     * value it takes — a step inside its open end, at six — {@code c} leaves {@code a} against
     * {@code s} one apart, and {@code s} stands at every {@code a} plus one and either side of
     * it. The end itself, which {@code c} does not take, would hold nothing.
     */
    @Test
    void aDecimalHeldStillStandsInsideAnEndItsRunLeavesOut() {
        NumericDomain.Bounds aboveFive = new NumericDomain.Bounds(Endpoint.exclusive(Count.of(5)),
                Endpoint.exclusive(Count.of(10)));
        NumericDomain.Bounds fromNought =
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)), null);
        List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                dense("a", 1, run(0, 10)), dense("c", 1, aboveFive), dense("s", -1, fromNought));

        assertEquals(new WhatARelationLeavesUndivided.Leaves.Undivided(),
                WhatARelationLeavesUndivided.leavesOf(terms, 0, ExactRatio.of(-5), Rel.GE,
                        String::equals, (one, other) -> true, Granularity.DENSE, null));
    }

    /**
     * The same relation of decimals, worked out by a program that can stop a row at something no
     * operation tells of: nothing is shown computed, so no term is left undivided and no run is
     * taken to settle it, whatever the terms' ends say.
     */
    @Test
    void aDenseTermIsShownNothingWhereTheProgramCanStopARowUntold() {
        NumericDomain.Bounds aboveFive = new NumericDomain.Bounds(Endpoint.exclusive(Count.of(5)),
                Endpoint.exclusive(Count.of(10)));
        NumericDomain.Bounds fromNought =
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)), null);
        List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                dense("a", 1, run(0, 10)), dense("c", 1, aboveFive), dense("s", -1, fromNought));

        assertNull(WhatARelationLeavesUndivided.leavesOf(terms, 0, ExactRatio.of(-5), Rel.GE,
                String::equals, (one, other) -> true, Granularity.DENSE, null, List.of(),
                new WhatARelationLeavesUndivided.Operations(List.of(),
                        WhatARelationLeavesUndivided.Told.SOME)));
    }

    /**
     * {@code a >= b} with {@code a} from nought to ten and {@code b} held at five: the runs that
     * settle it cover every value of {@code a}, so no value is left between them to be asked of
     * the program. They are still runs of rows only where the program gets to the end of working
     * them out, which a program that can stop a row untold does not show.
     */
    @Test
    void aDenseRunFullySettledByTheFormStillNeedsComputedRows() {
        List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                dense("a", 1, run(0, 10)), dense("b", -1, run(5, 5)));

        assertNull(WhatARelationLeavesUndivided.leavesOf(terms, 0, ExactRatio.ZERO, Rel.GE,
                String::equals, (one, other) -> true, Granularity.DENSE, null, List.of(),
                new WhatARelationLeavesUndivided.Operations(List.of(),
                        WhatARelationLeavesUndivided.Told.SOME)));
    }

    /**
     * {@code a + c - s >= 0} over {@code Int}s, {@code c} strictly between nought and two: held
     * still at one, the whole number inside its ends, {@code c} leaves {@code a} against
     * {@code s}. Where nothing says how the values of {@code c} are spaced, no value is shown
     * between those ends — whole, it would take none strictly between nought and one — and the
     * end it leaves out is no row to hold it at.
     */
    @Test
    void aTermWhoseSpacingIsNotSaidIsHeldAtNoValue() {
        List<WhatARelationLeavesUndivided.Leaves> leaves = new ArrayList<>();
        for (Granularity spacing : Arrays.asList(Granularity.DISCRETE, null)) {
            long high = spacing == null ? 1 : 2;
            NumericDomain.Bounds between = new NumericDomain.Bounds(
                    Endpoint.exclusive(Count.of(0)), Endpoint.exclusive(Count.of(high)));
            List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                    term("a", 1, run(0, 10), run(0, 10), null, true),
                    new WhatARelationLeavesUndivided.Term<>(List.of("c"), ExactRatio.ONE, between,
                            between, null, true, spacing, INTS),
                    term("s", -1, INTS, INTS, null, true));
            leaves.add(WhatARelationLeavesUndivided.leavesOf(terms, 0, ExactRatio.ZERO, Rel.GE,
                    String::equals, (one, other) -> true, Granularity.DISCRETE, GREATEST_INT));
        }
        assertEquals(new WhatARelationLeavesUndivided.Leaves.Undivided(), leaves.get(0));
        assertNotEquals(new WhatARelationLeavesUndivided.Leaves.Undivided(), leaves.get(1));
    }

    /** A decimal term at its place, taking every value of {@code run}, on an order with no end. */
    private static WhatARelationLeavesUndivided.Term<String> dense(String place, long weight,
                                                                  NumericDomain.Bounds run) {
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight), run,
                run, null, true, Granularity.DENSE, NumericDomain.Bounds.OPEN);
    }

    /** A type with no end, as a decimal is, leaves every difference one some value is apart by. */
    @Test
    void aTypeWithNoEndLeavesEveryDifference() {
        assertEquals(Set.of("a", "b"), WhatARelationLeavesUndivided.ofTheirDifference(
                pair(1, -1, A_DATE), ExactRatio.of(-10_000_000_000_000L), Rel.GT, List.of(),
                new WhatARelationLeavesUndivided.WhereTheRepresentationStops(
                        NumericDomain.Bounds.OPEN), String::equals, GREATEST_INT,
                WhatARelationLeavesUndivided.Operations.NONE, true));
    }

    /**
     * {@code Date.daysBetween(b, a) == 1}: moved together, the two are a day apart wherever they
     * stand, and only how far apart they are settles it. A date and a count of days are not moved
     * together: the count runs far past the last date.
     */
    @Test
    void twoValuesTakingTheSameValuesAreMovedTogetherByAnyConstant() {
        assertEquals(Set.of("a", "b"), apart(pair(1, -1, A_DATE), -1, Rel.EQ));
        assertEquals(Set.of(), apart(pair(1, -1, "Int"), -1, Rel.EQ));
    }

    /** {@code 2a - 2b <= 14} is about how far apart the two are; {@code 2a - b <= 14} is not, and
     *  an {@code a} past half the greatest value needs a {@code b} past the greatest. */
    @Test
    void twoWeightsMoveTwoValuesTogetherOnlyWhereOneIsTheOthersNegation() {
        assertEquals(Set.of("a", "b"), apart(pair(2, -2, A_DATE), -14, Rel.LE));
        assertEquals(Set.of(), apart(pair(2, -1, A_DATE), -14, Rel.LE));
    }

    /**
     * Weighed alike the two are about their sum, and read as the difference is: a sum no two dates
     * come to is no outcome, and one the middle date reaches either side of is. Weighed alike but
     * not by one, or one way and another by different amounts, they are neither.
     */
    @Test
    void twoValuesWeighedAlikeAreReadByTheirSum() {
        assertEquals(Set.of("a", "b"), apart(pair(1, 1, A_DATE), -14, Rel.EQ));
        assertEquals(Set.of("a", "b"), apart(pair(-1, -1, A_DATE), 14, Rel.GT));
        assertEquals(Set.of(), apart(pair(1, 1, A_DATE), -10_000_000_000_000L, Rel.EQ));
        assertEquals(Set.of(), apart(pair(2, 1, A_DATE), -14, Rel.EQ));
    }

    /** What the way holds of the sum is where it has to come out both ways, as of a difference. */
    @Test
    void whatTheWayHoldsOfTheSumIsWhereItHasToComeOutBothWays() {
        assertEquals(Set.of("a", "b"),
                apart(pair(1, 1, A_DATE), -14, Rel.EQ, held(1, -10, Rel.GE)));
        assertEquals(Set.of(),
                apart(pair(1, 1, A_DATE), -14, Rel.GT, held(1, -14, Rel.EQ)));
    }

    /**
     * Held at nought or more, the difference is at nought, where {@code a - b <= 0} holds, and at
     * one, where it fails. Held at nought to ten, every difference is at fourteen or less; held at
     * nought exactly, none is past fourteen.
     */
    @Test
    void whatTheWayHoldsOfTheDifferenceIsWhereItHasToComeOutBothWays() {
        assertEquals(Set.of("a", "b"),
                apart(pair(1, -1, A_DATE), 0, Rel.LE, held(1, 0, Rel.GE)));
        assertEquals(Set.of(),
                apart(pair(1, -1, A_DATE), -14, Rel.LE, held(1, 0, Rel.GE), held(1, -10, Rel.LE)));
        assertEquals(Set.of(),
                apart(pair(1, -1, A_DATE), -14, Rel.GT, held(1, 0, Rel.EQ)));
    }

    /** Held apart from fourteen, the difference is no run, and nothing is shown of it. */
    @Test
    void aDifferenceHeldApartFromOneValueShowsNothing() {
        assertEquals(Set.of(), apart(pair(1, -1, A_DATE), -14, Rel.EQ, held(1, -14, Rel.NE)));
        assertEquals(Set.of("a", "b"), apart(pair(1, -1, A_DATE), -14, Rel.EQ));
    }

    /**
     * Held apart from nought, the difference is below it or above it. {@code a - b < 0} holds in the
     * one and fails in the other, so it comes out either way; once the difference is also held at
     * nought or less, only the run below is left and it holds everywhere.
     */
    @Test
    void aDifferenceHeldApartFromOneValueComesOutAtTheRunsOnEitherSideOfIt() {
        assertEquals(Set.of("a", "b"), apart(pair(1, -1, A_DATE), 0, Rel.LT, held(1, 0, Rel.NE)));
        assertEquals(Set.of(), apart(pair(1, -1, A_DATE), 0, Rel.LT, held(1, 0, Rel.NE),
                held(1, 0, Rel.LE)));
    }

    /** {@code 2(a - b) - 1 != 0} is held by no whole difference, so it leaves every one of them. */
    @Test
    void aDifferenceHeldApartFromNoWholeNumberLeavesEveryWholeDifference() {
        assertEquals(Set.of("a", "b"), apart(pair(1, -1, A_DATE), 0, Rel.EQ, held(2, -1, Rel.NE)));
    }

    /**
     * {@code -(a - b) <= 0} holds the difference at nought or more, where {@code a - b + 1 <= 0}
     * never holds; {@code a - b <= 0} holds it at nought or less, where it holds at minus one and
     * fails at nought.
     */
    @Test
    void aNegativeWeightTurnsWhatAStatementHolds() {
        assertEquals(Set.of(), apart(pair(1, -1, A_DATE), 1, Rel.LE, held(-1, 0, Rel.LE)));
        assertEquals(Set.of("a", "b"), apart(pair(1, -1, A_DATE), 1, Rel.LE, held(1, 0, Rel.LE)));
    }

    /**
     * {@code 2(a - b) - 1 < 0} holds at a difference of nought and fails at one, both in a run from
     * nought to one; strictly between them is no whole difference, and nothing is shown.
     */
    @Test
    void onlyAWholeDifferenceIsAskedOf() {
        assertEquals(Set.of("a", "b"), apart(pair(2, -2, A_DATE), -1, Rel.LT,
                held(1, 0, Rel.GE), held(1, -1, Rel.LE)));
        assertEquals(Set.of(), apart(pair(2, -2, A_DATE), -1, Rel.LT,
                held(1, 0, Rel.GT), held(1, -1, Rel.LT)));
    }

    /**
     * {@code 2^62 x - y < 0}, {@code x} from nought to a hundred and {@code y} an {@code Int} read
     * as though its order ran on: at two, the true side needs a {@code y} past the greatest
     * {@code Int}. The run {@code y} has to stand in is a finite one, and still runs past where
     * {@code y}'s order stops, so {@code y} is no witness there. Held to a run inside its order —
     * a weight of one — it is.
     */
    @Test
    void aFiniteRunPastWhereTheReachingOrderStopsIsNoWitness() {
        var y = term("y", -1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN, null, true);
        var weighedPast = term("x", 1L << 62, run(0, 100), run(0, 100), null, true);
        var inside = term("x", 2, run(0, 100), run(0, 100), null, true);
        assertFalse(undivided(List.of(weighedPast, y), ExactRatio.ZERO, Rel.LT).contains("x"));
        assertTrue(undivided(List.of(inside, y), ExactRatio.ZERO, Rel.LT).contains("x"));
    }

    /**
     * {@code 2^62 x - 2^62 y < 0}, {@code y} any {@code Int}: at an {@code x} of nought a {@code y}
     * of one makes it true and one of nought false, and both rows are computed; at one, the true
     * side needs a {@code y} of two, which weighed passes the type. So {@code x} from nought to one
     * is not left either way at every value, and {@code x} at nought alone is.
     */
    @Test
    void aWitnessIsComputedAtEveryValueItIsAskedOfAndNotAtOne() {
        long k = 1L << 62;
        var y = term("y", -k, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN, null, true);
        var upToOne = term("x", k, run(0, 1), run(0, 1), null, true);
        var nought = term("x", k, run(0, 0), run(0, 0), null, true);
        assertFalse(undivided(List.of(upToOne, y), ExactRatio.ZERO, Rel.LT).contains("x"));
        assertTrue(undivided(List.of(nought, y), ExactRatio.ZERO, Rel.LT).contains("x"));
    }

    /**
     * Read by their difference, two terms weighed one leave rows past the type only beside its
     * ends; weighed two, every value past half the type has no row on one side, and weighed
     * {@code 2^62} nearly every value. Two dates weighed two are inside an {@code Int} at every
     * day, and stay shown.
     */
    @Test
    void aDifferenceUnderAWeightIsShownOnlyWhereItsRowsAreComputedAtEveryValue() {
        for (long weight : new long[] {1, 2, 1L << 62}) {
            var a = term("a", weight, INTS, NumericDomain.Bounds.OPEN, "same", true);
            var b = term("b", -weight, INTS, NumericDomain.Bounds.OPEN, "same", true);
            assertEquals(weight == 1 ? Set.of("a", "b") : Set.of(),
                    WhatARelationLeavesUndivided.ofTheirDifference(List.of(a, b), ExactRatio.ZERO,
                            Rel.LT, List.of(),
                            new WhatARelationLeavesUndivided.WhereTheRepresentationStops(INTS),
                            String::equals, GREATEST_INT,
                            WhatARelationLeavesUndivided.Operations.NONE, true),
                    "Ints weighed " + weight);
        }
        assertEquals(Set.of("a", "b"), apart(pair(2, -2, A_DATE), 0, Rel.LT));
    }

    /**
     * {@code x - y + z - 1000 > 0}, {@code z} read as though its order ran on but counted on an
     * order stopping at a hundred: brought to nought by a {@code z} of a thousand, the rest would
     * leave {@code x} to {@code y}, and no {@code z} is there. Counted on an order reaching a
     * thousand, it is. {@code y} stops at ten: with no end it would reach both sides beside a
     * {@code z} at nought, where the constant stays in the row.
     */
    @Test
    void aTermIsHeldOnlyAtAValueItsOrderHolds() {
        var x = term("x", 1, run(0, 10), run(0, 10), null, true);
        var y = term("y", -1, run(0, 10), run(0, 10), null, true);
        var shortOrder = runningTo(run(0, 100), "z", 1, NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, null, true);
        var longOrder = runningTo(run(0, 1000), "z", 1, NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, null, true);
        ExactRatio constant = ExactRatio.of(-1000);
        assertFalse(undivided(List.of(x, y, shortOrder), constant, Rel.GT).contains("x"));
        assertTrue(undivided(List.of(x, y, longOrder), constant, Rel.GT).contains("x"));
    }
}
