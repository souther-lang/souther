package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether an order has a place at a level for a line to be, which is not whether it takes it.
 *
 * <p>Two questions, and one answer served both. Whether the quantity takes the level is
 * {@code attainable}, and a rule may cut where it takes nothing: {@code 2 * a <= 9} parts the even
 * numbers between eight and ten, and nine is neither. So a reader may not refuse a line for the
 * level being unattainable — and it still has to refuse one at a level the order has no room for at
 * all.
 *
 * <p>Asked of the order because that is what knows. Asked of the carrier instead — "do these values
 * count" — a property of the values stood in for a property of the places, and two strings, which
 * stand no measurable distance apart and are still one above the other, were left with no line at
 * the place they meet.
 */
class AnOrderSaysWhereALineCanBeAtAllTest {

    private static Level at(long count) {
        return new Level.ACount(new Count(BigDecimal.valueOf(count)));
    }

    /** An order that steps is parted anywhere, including where it takes nothing. */
    @Test
    void anOrderThatCountsIsPartedAtALevelItDoesNotTake() {
        LevelSpace evens = LevelSpace.steppingBy(BigDecimal.TWO);

        assertTrue(evens.canCutAt(at(9)),
                "the even numbers part between eight and ten, which is a line at nine");
        assertFalse(evens.attainable(at(9)),
                "and nine is not one of them, which is the other question");
    }

    /** An order whose only number is where two positions meet has one place and no others. */
    @Test
    void anOrderWithOnePlaceIsPartedThereAndNowhereElse() {
        LevelSpace meeting = LevelSpace.onlyWhereTheyMeet();

        assertTrue(meeting.canCutAt(at(0)), "two strings are equal or they are not");
        assertFalse(meeting.canCutAt(at(1)),
                "and a rule holding them one apart asks for a line this order has no place for");
    }
}
