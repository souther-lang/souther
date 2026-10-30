package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.Independence;
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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A count that moves a date is related to a relation of the moved date where some date the term is
 * shown to take lets every run complete, and by nothing less: not a date the term merely may take,
 * not a date held out of the dates now held, not a count that is not one the term takes, and not
 * two terms that are made of one place or tied to each other.
 */
class ACountMovingADateRelatesOnlyWhereARowShownToBeTakenCompletesTest {

    private static final long LEAST = -365_243_219_162L;
    private static final long GREATEST = 365_241_780_471L;
    private static final long YEAR_2027 = 20_819L;
    private static final long COUNTS = 730_484_999_633L;
    private static final long PAST_THE_YEAR = YEAR_2027 - LEAST;

    private static final BiPredicate<String, String> SEPARATE = String::equals;
    private static final Independence UNTIED = (one, other) -> true;

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

    private static Term<String> days(NumericDomain.Bounds realizes) {
        return term("days", run(-COUNTS, COUNTS), realizes);
    }

    private static Term<String> birthday(NumericDomain.Bounds holds,
                                         NumericDomain.Bounds realizes) {
        return term("birthday", holds, realizes);
    }

    private static Operations moved() {
        IntSum sum = new IntSum(Map.of("birthday", ExactRatio.ONE, "days", ExactRatio.ONE),
                ExactRatio.ZERO, BigInteger.valueOf(LEAST), BigInteger.valueOf(GREATEST));
        return Operations.read(List.of(sum), true);
    }

    private static Leaves leavesOf(Independence independent) {
        return WhatARelationLeavesUndivided.leavesOf(
                List.of(birthday(run(LEAST, GREATEST), run(LEAST, GREATEST)),
                        days(run(-COUNTS, COUNTS))),
                1, ExactRatio.of(-YEAR_2027), Rel.GE, SEPARATE, independent,
                Granularity.DISCRETE, BigInteger.valueOf(Long.MAX_VALUE), List.of(), moved());
    }

    /**
     * The date nearest nought stops at a count past the calendar's length, and a date at the
     * calendar's other end does not: the count is related, from the counts that move every date the
     * date takes past the year to the ones that move every date short of it.
     */
    @Test
    void aCountThatSomeDateTheTermTakesCompletesIsRelated() {
        Leaves.Settled settled = (Leaves.Settled) leavesOf(UNTIED);

        assertEquals(2, settled.runs().size(), settled.toString());
        assertFalse(settled.runs().getFirst().holds(), settled.toString());
        assertTrue(settled.runs().getLast().holds(), settled.toString());
        assertEquals(BigInteger.valueOf(PAST_THE_YEAR), settled.runs().getLast().from().at()
                .floor().orNull(), settled.toString());
    }

    /** Two dates tied to each other are not two the rows stand at as they like. */
    @Test
    void aCountAndADateTiedToEachOtherAreNotRelatedByTheDatesAlone() {
        assertNull(leavesOf((one, other) -> false));
    }

    private static boolean someDateCompletes(Term<String> birthday, Term<String> days,
                                             long count, BiPredicate<String, String> overlap,
                                             Independence independent) {
        return WhatARelationLeavesUndivided.theOtherTermCompletesTheRow(
                RowsComputed.upTo(null).withOperations(moved()), List.of(birthday, days), 1,
                ExactRatio.of(count), overlap, independent);
    }

    private static boolean someDateCompletes(NumericDomain.Bounds birthdayHolds,
                                             NumericDomain.Bounds birthdayRealizes) {
        return someDateCompletes(birthday(birthdayHolds, birthdayRealizes),
                days(run(-COUNTS, COUNTS)), PAST_THE_YEAR, SEPARATE, UNTIED);
    }

    @Test
    void aDateTheTermIsShownToTakeCompletesTheCount() {
        assertTrue(someDateCompletes(run(LEAST, GREATEST), run(LEAST, GREATEST)));
        assertTrue(someDateCompletes(run(LEAST, GREATEST), run(LEAST, LEAST + 10)));
    }

    /** What a date may be is no date it is shown to be: a date only held is no row for the count. */
    @Test
    void datesOnlyHeldAreNoRowForTheCount() {
        assertFalse(someDateCompletes(run(LEAST, GREATEST), null));
    }

    /** Dates the term is shown to take, at none of which the count completes. */
    @Test
    void datesShownTakenAtNoneOfWhichTheCountCompletesAreNoRowForIt() {
        assertFalse(someDateCompletes(run(LEAST, GREATEST), run(0, 10)));
    }

    /** The dates shown to be taken, cut to the dates the term is now held to. */
    @Test
    void datesTheTermIsNoLongerHeldToAreNoRowForTheCount() {
        assertFalse(someDateCompletes(run(0, 10), run(LEAST, GREATEST)));
    }

    /** A count the term is not shown to take is not one the row stands at. */
    @Test
    void aCountTheTermIsNotShownToTakeIsNoRow() {
        Term<String> birthday = birthday(run(LEAST, GREATEST), run(LEAST, GREATEST));

        assertFalse(someDateCompletes(birthday, days(null), PAST_THE_YEAR, SEPARATE, UNTIED));
        assertFalse(someDateCompletes(birthday, days(run(0, 100)), PAST_THE_YEAR, SEPARATE,
                UNTIED));
        assertTrue(someDateCompletes(birthday, days(run(0, COUNTS)), PAST_THE_YEAR, SEPARATE,
                UNTIED));
    }

    /** Where the date and the count are made of one place, a date at an end is not a date the count
     *  goes with. */
    @Test
    void termsMadeOfOnePlaceAreNotPlacedApart() {
        assertFalse(someDateCompletes(birthday(run(LEAST, GREATEST), run(LEAST, GREATEST)),
                days(run(-COUNTS, COUNTS)), PAST_THE_YEAR, (one, other) -> true, UNTIED));
    }

    /** Two terms of different places that move together: the numbers say a row completes, and the
     *  row is none of the terms'. */
    @Test
    void termsTiedToEachOtherAreNotPlacedIndependently() {
        assertFalse(someDateCompletes(birthday(run(LEAST, GREATEST), run(LEAST, GREATEST)),
                days(run(-COUNTS, COUNTS)), PAST_THE_YEAR, SEPARATE, (one, other) -> false));
    }
}
