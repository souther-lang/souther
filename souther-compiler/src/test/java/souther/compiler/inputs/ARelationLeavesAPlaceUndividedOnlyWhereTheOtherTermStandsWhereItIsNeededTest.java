package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

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
                realizes, takes, itsPlace);
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
     * is, so the two taking the same values does not leave it undivided. Held to be one value, each
     * is the other's.
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
     *  below the least, which no value is. */
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
}
