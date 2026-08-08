package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a range stops, and whether the value it stops at is one of its own.
 *
 * <p>The algebra is written here once because two carriers derive it: the domain, which computes
 * with the numbers, and a partition's end, which also says which rule put it there. Two inventions
 * of the same rule is the disagreement this exists to keep out.
 */
class EndpointTest {

    private static final BigDecimal FIVE = new BigDecimal("5");

    /**
     * Two lower bounds at the same value leave the value out where either of them does.
     *
     * <p>{@code x >= 5} and {@code x > 5} together are {@code x > 5}: the second refuses the value,
     * and a conjunction cannot admit what one of its conjuncts refuses.
     */
    @Test
    void theExclusiveOfTwoLowerBoundsAtOneValueWins() {
        Endpoint open = Endpoint.exclusive(FIVE);
        Endpoint closed = Endpoint.inclusive(FIVE);

        assertEquals(open, Endpoint.lower(closed, open));
        assertEquals(open, Endpoint.lower(open, closed));
    }

    /** The same of two upper bounds, which differ only in which way the values run. */
    @Test
    void theExclusiveOfTwoUpperBoundsAtOneValueWins() {
        Endpoint open = Endpoint.exclusive(FIVE);
        Endpoint closed = Endpoint.inclusive(FIVE);

        assertEquals(open, Endpoint.upper(closed, open));
        assertEquals(open, Endpoint.upper(open, closed));
    }

    /**
     * An end is not moved by one that says the same thing.
     *
     * <p>Two readings of one range reach it by different routes and write their numbers to different
     * places — a rule read off the declaration says zero, the same rule projected through the record
     * says zero to one place. Neither is tighter, so neither replaces the other, and what a report
     * prints does not depend on which reading was asked second.
     */
    @Test
    void anEndIsKeptWhereTheOtherIsNoTighter() {
        Endpoint had = Endpoint.inclusive(new BigDecimal("0"));
        Endpoint same = Endpoint.inclusive(new BigDecimal("0.0"));

        assertEquals(had, Endpoint.lower(had, same));
        assertEquals(had, Endpoint.upper(had, same));
    }

    /**
     * Ends at one value leave that value where either of them refuses it, and nothing else is there.
     *
     * <p>Asked here rather than of the two numbers, which are equal in all four and say nothing about
     * whether anything is left. Over a dense atom there is nothing between them to fall back on.
     */
    @Test
    void endsAtOneValueAdmitItOnlyWhereBothDo() {
        Endpoint open = Endpoint.exclusive(FIVE);
        Endpoint closed = Endpoint.inclusive(FIVE);

        assertTrue(Endpoint.someValueLiesBetween(closed, closed));
        assertFalse(Endpoint.someValueLiesBetween(open, closed));
        assertFalse(Endpoint.someValueLiesBetween(closed, open));
        assertFalse(Endpoint.someValueLiesBetween(open, open));
    }
}
