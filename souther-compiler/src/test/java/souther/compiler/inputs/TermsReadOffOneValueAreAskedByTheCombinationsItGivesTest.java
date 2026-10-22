package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.JointSupport;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Terms read off one value are asked by the combinations of values that value gives, and by
 * nothing between them.
 *
 * <p>A month and a day of one date are two numbers that overlap, so they are no two apart terms.
 * Given the months and days a date has, each month is a value at which the relation comes out
 * either way, because the combinations that go with the month are what the others are added to.
 */
class TermsReadOffOneValueAreAskedByTheCombinationsItGivesTest {

    private static final BigInteger GREATEST_INT = BigInteger.valueOf(Long.MAX_VALUE);

    private static final int[] DAYS_OF_A_MONTH = {31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};

    private static NumericDomain.Bounds run(long low, long high) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(low)),
                Endpoint.inclusive(Count.of(high)));
    }

    private static WhatARelationLeavesUndivided.Term<String> term(String place, long weight,
                                                                 long low, long high) {
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight),
                run(low, high), run(low, high), null, false, Granularity.DISCRETE,
                run(Long.MIN_VALUE, Long.MAX_VALUE));
    }

    /** Every month and day a date has, as the combinations of a support over a month and a day. */
    private static List<List<ExactRatio>> monthsAndDays(boolean withTheThirtiethOfFebruary) {
        List<List<ExactRatio>> out = new ArrayList<>();
        for (int month = 1; month <= 12; month++) {
            int days = DAYS_OF_A_MONTH[month - 1];
            for (int day = 1; day <= days; day++) {
                out.add(List.of(ExactRatio.of(month), ExactRatio.of(day)));
            }
        }
        if (withTheThirtiethOfFebruary) {
            out.add(List.of(ExactRatio.of(2), ExactRatio.of(30)));
        }
        return out;
    }

    private static Leaves leavesOf(List<WhatARelationLeavesUndivided.Term<String>> terms, int at,
                                   long constant, Rel relation, List<JointSupport> supports) {
        return leavesOf(terms, at, constant, relation, supports, GREATEST_INT);
    }

    private static Leaves leavesOf(List<WhatARelationLeavesUndivided.Term<String>> terms, int at,
                                   long constant, Rel relation, List<JointSupport> supports,
                                   BigInteger greatest) {
        return WhatARelationLeavesUndivided.leavesOf(terms, at, ExactRatio.of(constant), relation,
                String::equals, (one, other) -> true, Granularity.DISCRETE, greatest, supports);
    }

    /**
     * {@code 100 * month(on) + day(on) < 100 * month(birthday) + day(birthday)}: no term alone is
     * reached on both sides, and each is once the dates' own combinations are what the others are
     * asked by.
     */
    @Test
    void theMonthAndTheDayOfOneDateAreAskedByTheMonthsAndDaysThatDateHas() {
        var terms = List.of(term("on", 100, 1, 12), term("on", 1, 1, 31),
                term("birthday", -100, 1, 12), term("birthday", -1, 1, 31));
        var supports = List.of(new JointSupport(List.of(0, 1), monthsAndDays(false)),
                new JointSupport(List.of(2, 3), monthsAndDays(false)));
        for (int at = 0; at < terms.size(); at++) {
            assertInstanceOf(Leaves.Undivided.class, leavesOf(terms, at, 0, Rel.LT, supports),
                    "term " + at);
            assertFalse(leavesOf(terms, at, 0, Rel.LT, List.of()) instanceof Leaves.Undivided,
                    "term " + at + " without the dates' combinations");
        }
    }

    /**
     * A witness is a row that is computed. Each date's part of a row is at most a hundred times
     * twelve and thirty-one, so the rows the combinations give are computed where the type holds
     * both dates' parts added, and are no witnesses one short of that.
     */
    @Test
    void theCombinationsAreNoWitnessesWhereTheirRowsPassWhereTheTypeStops() {
        var terms = List.of(term("on", 100, 1, 12), term("on", 1, 1, 31),
                term("birthday", -100, 1, 12), term("birthday", -1, 1, 31));
        var supports = List.of(new JointSupport(List.of(0, 1), monthsAndDays(false)),
                new JointSupport(List.of(2, 3), monthsAndDays(false)));
        BigInteger bothDates = BigInteger.valueOf(2 * (100 * 12 + 31));
        for (int at = 0; at < terms.size(); at++) {
            assertInstanceOf(Leaves.Undivided.class,
                    leavesOf(terms, at, 0, Rel.LT, supports, bothDates), "term " + at);
            assertFalse(leavesOf(terms, at, 0, Rel.LT, supports,
                    bothDates.subtract(BigInteger.ONE)) instanceof Leaves.Undivided,
                    "term " + at + " where the type stops one short of both dates");
        }
    }

    /**
     * {@code month + day < 32}: February has no day past the twenty-ninth, so at February every
     * sum is below thirty-two and the month settles the relation. A combination of February and
     * the thirtieth is the one that makes it come out the other way, so the answer is the
     * combinations' and not the ends' of the month and of the day.
     */
    @Test
    void aCombinationTheDateDoesNotGiveIsNotAWitness() {
        var terms = List.of(term("on", 1, 1, 12), term("on", 1, 1, 31));
        var calendar = List.of(new JointSupport(List.of(0, 1), monthsAndDays(false)));
        var withAnImpossibleDay = List.of(new JointSupport(List.of(0, 1), monthsAndDays(true)));
        assertFalse(leavesOf(terms, 0, -32, Rel.LT, calendar) instanceof Leaves.Undivided);
        assertEquals(new Leaves.Undivided(), leavesOf(terms, 0, -32, Rel.LT, withAnImpossibleDay));
    }

    /** Terms of a support that another term is tied to are not asked together with it. */
    @Test
    void aTermTiedToAnotherGroupIsNotAskedBesideIt() {
        var terms = List.of(term("on", 100, 1, 12), term("on", 1, 1, 31),
                term("birthday", -100, 1, 12), term("birthday", -1, 1, 31));
        var supports = List.of(new JointSupport(List.of(0, 1), monthsAndDays(false)),
                new JointSupport(List.of(2, 3), monthsAndDays(false)));
        assertFalse(WhatARelationLeavesUndivided.leavesOf(terms, 0, ExactRatio.of(0), Rel.LT,
                String::equals, (one, other) -> one + other != 2 && one + other != 3,
                Granularity.DISCRETE, GREATEST_INT, supports) instanceof Leaves.Undivided);
    }
}
