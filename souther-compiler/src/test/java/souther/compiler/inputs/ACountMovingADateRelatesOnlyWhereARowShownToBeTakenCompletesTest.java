package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.IntSum;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Term;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.function.BiPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A count that moves a date is related to a relation of the moved date where some date the term is
 * shown to take lets every run complete, and by nothing less: not a date the term merely may take,
 * and not one of two terms made of the same place.
 */
class ACountMovingADateRelatesOnlyWhereARowShownToBeTakenCompletesTest {

    private static final long LEAST = -365_243_219_162L;
    private static final long GREATEST = 365_241_780_471L;
    private static final long YEAR_2027 = 20_819L;

    private static NumericDomain.Bounds run(long low, long high) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(low)),
                Endpoint.inclusive(Count.of(high)));
    }

    private static final NumericDomain.Bounds INTS = run(Long.MIN_VALUE, Long.MAX_VALUE);

    private static Term<String> term(String place, NumericDomain.Bounds holds,
                                     NumericDomain.Bounds realizes) {
        return new Term<>(List.of(place), ExactRatio.ONE, holds, realizes, null, true,
                Granularity.DISCRETE, INTS, place);
    }

    private static Leaves daysOf(NumericDomain.Bounds birthdayRealizes,
                                 BiPredicate<String, String> overlap) {
        Term<String> birthday = term("birthday", run(LEAST, GREATEST), birthdayRealizes);
        Term<String> days = term("days", run(-730_484_999_633L, 730_484_999_633L),
                run(-730_484_999_633L, 730_484_999_633L));
        IntSum moved = new IntSum(Map.of("birthday", ExactRatio.ONE, "days", ExactRatio.ONE),
                ExactRatio.ZERO, BigInteger.valueOf(LEAST), BigInteger.valueOf(GREATEST));
        return WhatARelationLeavesUndivided.leavesOf(List.of(birthday, days), 1,
                ExactRatio.of(-YEAR_2027), Rel.GE, overlap, (one, other) -> true,
                Granularity.DISCRETE, BigInteger.valueOf(Long.MAX_VALUE), List.of(),
                Operations.read(List.of(moved), true));
    }

    /**
     * The date nearest nought stops at a count past the calendar's length, and a date at the
     * calendar's other end does not: the count is related, from the counts that move every date the
     * date takes past the year to the ones that move every date short of it.
     */
    @Test
    void aCountThatSomeDateTheTermTakesCompletesIsRelated() {
        Leaves.Settled settled =
                (Leaves.Settled) daysOf(run(LEAST, GREATEST), String::equals);

        assertEquals(2, settled.runs().size(), settled.toString());
        assertFalse(settled.runs().getFirst().holds(), settled.toString());
        assertTrue(settled.runs().getLast().holds(), settled.toString());
        assertEquals(BigInteger.valueOf(YEAR_2027 - LEAST), settled.runs().getLast().from().at()
                .floor().orNull(), settled.toString());
    }

    /** What a date may be is no date it is shown to be: a date only held is no row for the count. */
    @Test
    void datesOnlyHeldAreNoRowForTheCount() {
        assertFalse(someDateCompletes(null, String::equals));
        assertTrue(someDateCompletes(run(LEAST, GREATEST), String::equals));
    }

    /** Dates the term is shown to take, at none of which the count completes. */
    @Test
    void datesShownTakenAtNoneOfWhichTheCountCompletesAreNoRowForIt() {
        assertFalse(someDateCompletes(run(0, 10), String::equals));
        assertTrue(someDateCompletes(run(LEAST, LEAST + 10), String::equals));
    }

    /** Where the date and the count are made of one place, a date at an end is not a date the count
     *  goes with. */
    @Test
    void termsMadeOfOnePlaceAreNotPlacedApart() {
        assertFalse(someDateCompletes(run(LEAST, GREATEST), (one, other) -> true));
    }

    /** Whether the count at the least that moves every date past the year has a date that completes. */
    private static boolean someDateCompletes(NumericDomain.Bounds birthdayRealizes,
                                             BiPredicate<String, String> overlap) {
        Term<String> birthday = term("birthday", run(LEAST, GREATEST), birthdayRealizes);
        Term<String> days = term("days", run(-730_484_999_633L, 730_484_999_633L),
                run(-730_484_999_633L, 730_484_999_633L));
        IntSum moved = new IntSum(Map.of("birthday", ExactRatio.ONE, "days", ExactRatio.ONE),
                ExactRatio.ZERO, BigInteger.valueOf(LEAST), BigInteger.valueOf(GREATEST));
        return WhatARelationLeavesUndivided.theOtherTermCompletesTheRow(
                RowsComputed.upTo(null).withOperations(Operations.read(List.of(moved), true)),
                List.of(birthday, days), 1, ExactRatio.of(YEAR_2027 - LEAST), overlap);
    }
}
