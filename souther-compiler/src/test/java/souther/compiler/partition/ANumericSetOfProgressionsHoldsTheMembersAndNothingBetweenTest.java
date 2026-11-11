package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.numeric.WholeNumberSet;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A class of the numbers a weighed number can be is asked by membership: the even numbers hold ten
 * and not eleven, whatever the ends of the type, and the ends of the run they lie in are no claim
 * that what is between them is held.
 */
class ANumericSetOfProgressionsHoldsTheMembersAndNothingBetweenTest {

    private static NumericSet.InTheNumbers evens() {
        return new NumericSet.InTheNumbers(WholeNumberSet.ofClass(
                new Congruences(BigInteger.ZERO, BigInteger.TWO)));
    }

    @Test
    void anEvenNumberIsHeldAndAnOddOneIsNot() {
        NumericSet evens = evens();
        assertTrue(evens.holds(Count.of(10), Carrier.WHOLE));
        assertTrue(evens.holds(Count.of(-4), Carrier.WHOLE));
        assertTrue(evens.holds(Count.of(0), Carrier.WHOLE));
        assertFalse(evens.holds(Count.of(11), Carrier.WHOLE));
        assertFalse(evens.holds(Count.of(-3), Carrier.WHOLE));
    }

    @Test
    void theEndsOfIntAreHeldWhereTheirRemainderIs() {
        NumericSet evens = evens();
        assertTrue(evens.holds(Count.of(Integer.MIN_VALUE), Carrier.WHOLE));
        assertFalse(evens.holds(Count.of(Integer.MAX_VALUE), Carrier.WHOLE));
        assertTrue(evens.holds(Count.of(Integer.MAX_VALUE - 1L), Carrier.WHOLE));
    }

    /** A number that is no whole number is none of the members, however near one it is. */
    @Test
    void aNumberWithADecimalPartIsNoMember() {
        assertFalse(evens().holds(Count.of(new BigDecimal("2.5")), Carrier.WHOLE));
        assertTrue(evens().holds(Count.of(new BigDecimal("2.0")), Carrier.WHOLE));
    }

    @Test
    void theRunTheyLieInIsNotTheSetAndNoRunHoldsOnlyThem() {
        NumericSet fromZero = new NumericSet.InTheNumbers(evens().numbers().and(
                WholeNumberSet.ofRuns(WholeNumberRuns.one(BigInteger.ZERO, null))));
        assertEquals(Count.of(0), fromZero.extent().min().at());
        assertNull(fromZero.extent().max());
        assertNull(fromZero.asOneRun());
        assertFalse(fromZero.holds(Count.of(3), Carrier.WHOLE));
    }

    @Test
    void aClassHoldsSomeNumber() {
        assertThrows(IllegalArgumentException.class,
                () -> new NumericSet.InTheNumbers(WholeNumberSet.NONE));
    }
}
