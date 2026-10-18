package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.time.LocalDate;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

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

    private static WhatARelationLeavesUndivided.Term<String> term(String place, long weight,
                                                                 NumericDomain.Bounds holds,
                                                                 NumericDomain.Bounds realizes,
                                                                 Object takes, boolean itsPlace) {
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight), holds,
                realizes, takes, itsPlace, Granularity.DISCRETE);
    }

    private static Set<String> undivided(List<WhatARelationLeavesUndivided.Term<String>> terms,
                                         ExactRatio constant, Rel relation) {
        return WhatARelationLeavesUndivided.of(terms, constant, relation, String::equals,
                (one, other) -> true);
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
    private static final NumericDomain.Bounds DATES =
            run(LocalDate.MIN.toEpochDay(), LocalDate.MAX.toEpochDay());

    private static Set<String> apart(List<WhatARelationLeavesUndivided.Term<String>> terms,
                                     long constant, Rel relation,
                                     WhatARelationLeavesUndivided.OnTheDifference... held) {
        return WhatARelationLeavesUndivided.ofTheirDifference(terms, ExactRatio.of(constant),
                relation, List.of(held), DATES, String::equals);
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

    /** A type with no end, as a decimal is, leaves every difference one some value is apart by. */
    @Test
    void aTypeWithNoEndLeavesEveryDifference() {
        assertEquals(Set.of("a", "b"), WhatARelationLeavesUndivided.ofTheirDifference(
                pair(1, -1, A_DATE), ExactRatio.of(-10_000_000_000_000L), Rel.GT, List.of(),
                NumericDomain.Bounds.OPEN, String::equals));
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
}
