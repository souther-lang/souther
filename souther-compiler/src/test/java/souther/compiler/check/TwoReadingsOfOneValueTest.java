package souther.compiler.check;

import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Every reading of one helper parameter, and what they settle between them. A variable is what a
 * reading leaves open, so it yields to what another reading says there — but it says one thing
 * everywhere it stands, none of the readings is the one being checked, and a reading that says what
 * a variable is may arrive after the readings that used it.
 */
class TwoReadingsOfOneValueTest {

    private static Type v(String name) {
        return Type.inferredVar(name);
    }

    private static Type pair(Type a, Type b) {
        return Type.tuple(List.of(a, b));
    }

    @Test
    void whatOneReadingStatesAndTheOtherLeavesOpenIsStated() {
        assertEquals(Type.list(Type.INT), Readings.of(Type.list(v("a")), Type.list(Type.INT)));
        assertEquals(Type.list(Type.INT), Readings.of(Type.list(Type.INT), Type.list(v("a"))));
    }

    @Test
    void twoAnswersAboutWhatTheValueIsAreNotOneLeftOpen() {
        assertNull(Readings.of(Type.list(Type.INT), Type.set(Type.INT)));
        assertNull(Readings.of(Type.list(Type.INT), Type.list(Type.STRING)));
        assertNull(Readings.of(pair(Type.INT, Type.INT),
                Type.tuple(List.of(Type.INT, Type.INT, Type.INT))));
    }

    /** A variable says one thing everywhere it stands, so a second appearance meets the first. */
    @Test
    void oneVariableStandingTwiceHoldsOneType() {
        assertNull(Readings.of(pair(v("a"), v("a")), pair(Type.INT, Type.STRING)));
        assertEquals(pair(Type.INT, Type.INT),
                Readings.of(pair(v("a"), v("a")), pair(Type.INT, Type.INT)));
    }

    /** A variable's earlier reading is itself a reading, so the two are taken together rather than
     * compared: what one position said it holds answers the position that left it open. */
    @Test
    void whatAVariableStoodForAlreadyIsReadWithWhatItStandsForNow() {
        assertEquals(Type.map(Type.STRING, Type.STRING),
                Readings.of(Type.map(v("a"), v("a")), Type.map(Type.STRING, v("b"))));
        assertEquals(pair(Type.INT, Type.INT),
                Readings.of(pair(v("a"), v("a")), pair(Type.INT, v("b"))));
    }

    /** Nothing built from a value holds that value, so a reading saying so is not one to take. */
    @Test
    void aVariableDoesNotStandForSomethingHoldingItself() {
        assertNull(Readings.of(v("a"), Type.list(v("a"))));
        assertNull(Readings.of(Type.list(v("a")), v("a")));
        assertNull(Readings.of(v("a"), pair(Type.INT, v("a"))));
    }

    /**
     * What one reading said about a variable is still said when the next reading arrives. Readings
     * are taken one at a time as the walk finds them, so a relation two of them settle has to reach
     * the third: {@code a} is {@code b} and {@code b} is a list of {@code b} cannot both hold,
     * whichever pair is put together first.
     */
    @Test
    void whatTwoReadingsSettledIsStillSettledWhenTheThirdArrives() {
        assertNull(Readings.of(List.of(v("a"), v("b"), Type.list(v("b")))));
        assertNull(Readings.of(List.of(Type.list(v("b")), v("b"), v("a"))));

        Type ab = pair(v("a"), v("b"));
        Type ba = pair(v("b"), v("a"));
        Type intA = pair(Type.INT, v("a"));
        assertEquals(pair(Type.INT, Type.INT), Readings.of(List.of(ab, ba, intA)));
        assertEquals(pair(Type.INT, Type.INT), Readings.of(List.of(ab, intA, ba)));
        assertEquals(pair(Type.INT, Type.INT), Readings.of(List.of(ba, intA, ab)));
        assertEquals(pair(Type.INT, Type.INT), Readings.of(List.of(intA, ab, ba)));
    }

    /**
     * A position settled late settles the same value read earlier. The readings say {@code a} is a
     * pair of {@code b}s and that one of those is an Int, so both of them are, wherever they were
     * read.
     */
    @Test
    void aPositionSettledLateSettlesTheSameValueReadEarlier() {
        Type a = v("a");
        Type b = v("b");
        Type bb = pair(b, b);
        Type bInt = pair(b, Type.INT);
        Type ints = pair(Type.INT, Type.INT);
        assertEquals(ints, Readings.of(List.of(a, bb, bInt)));
        assertEquals(ints, Readings.of(List.of(bInt, bb, a)));
        assertEquals(ints, Readings.of(List.of(bb, a, bInt)));
    }

    /**
     * What a variable comes to is settled through what it is settled to, so a value holds itself
     * whichever of the two positions says so. {@code (a, a)} beside {@code (List<b>, b)} says
     * {@code a} is a list of {@code b} and also that {@code a} is {@code b}.
     */
    @Test
    void aValueSettledThroughAnotherVariableStillCannotHoldItself() {
        Type aa = pair(v("a"), v("a"));
        Type listBAndB = pair(Type.list(v("b")), v("b"));
        assertNull(Readings.of(aa, listBAndB));
        assertNull(Readings.of(listBAndB, aa));
    }

    /**
     * A parameter whose readings cannot be one value settles nothing for the parameters after it.
     * A constructor is taken apart one position at a time, so what the positions before a
     * disagreement settled is written while it is still open whether the readings agree at all.
     */
    @Test
    void aParameterThatSettlesNothingLeavesNothingSettled() {
        Type a = v("a");
        Readings all = new Readings();
        all.add(pair(a, Type.INT));
        all.add(pair(Type.STRING, Type.BOOL));
        assertNull(all.answer(), "an Int and a Bool are not one value");

        all.forParameter();
        all.add(a);
        assertEquals(a, all.answer(), "`a` is what it was; the refused reading is not evidence");
    }

    /** Neither reading is the one being checked, so which is given first decides nothing. */
    @Test
    void theAnswerIsTheSameWhicheverReadingIsGivenFirst() {
        List<Type[]> pairs = List.of(
                new Type[] {pair(v("a"), v("a")), pair(Type.INT, Type.STRING)},
                new Type[] {pair(v("a"), v("a")), pair(v("b"), v("c"))},
                new Type[] {pair(v("a"), v("b")), pair(v("c"), v("c"))},
                new Type[] {Type.list(v("a")), Type.list(Type.INT)},
                new Type[] {Type.map(v("a"), v("a")), Type.map(Type.STRING, Type.INT)},
                new Type[] {Type.list(Type.INT), Type.set(Type.INT)},
                new Type[] {Type.option(v("a")), Type.option(v("a"))},
                new Type[] {Type.map(v("a"), v("a")), Type.map(Type.STRING, v("b"))},
                new Type[] {pair(v("a"), v("b")), pair(v("c"), v("c"))},
                new Type[] {v("a"), Type.list(v("a"))});
        for (Type[] two : pairs) {
            assertEquals(Readings.of(two[0], two[1]), Readings.of(two[1], two[0]),
                    Type.show(two[0]) + " with " + Type.show(two[1]));
        }
    }

    /** Several readings are folded pairwise, so the order they arrive in decides nothing either. */
    @Test
    void foldingThreeReadingsDoesNotDependOnTheOrderTheyArriveIn() {
        Type a = Type.list(v("a"));
        Type b = Type.list(Type.INT);
        Type c = Type.list(v("b"));
        assertEquals(Readings.of(List.of(a, b, c)), Readings.of(List.of(c, b, a)));

        Type wide = pair(v("a"), v("a"));
        Type ints = pair(Type.INT, Type.INT);
        Type mixed = pair(Type.INT, Type.STRING);
        assertNull(Readings.of(List.of(wide, ints, mixed)));
        assertNull(Readings.of(List.of(mixed, ints, wide)));
        assertNull(Readings.of(List.of(ints, mixed, wide)));
    }
}
