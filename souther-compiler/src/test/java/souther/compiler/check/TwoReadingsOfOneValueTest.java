package souther.compiler.check;

import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Taking two readings of one helper parameter together. A variable is what a reading leaves open, so
 * it yields to what the other reading says there — but it says one thing everywhere it stands, and
 * neither reading is the one being checked against the other.
 */
class TwoReadingsOfOneValueTest {

    private static final BindingId OWNER =
            new BindingId(new BindingOwner.OfData(new TypeName("demo", "X")), 0);

    private static Type v(String name) {
        return Type.mintedVar(name, OWNER);
    }

    private static Type pair(Type a, Type b) {
        return Type.tuple(List.of(a, b));
    }

    @Test
    void whatOneReadingStatesAndTheOtherLeavesOpenIsStated() {
        assertEquals(Type.list(Type.INT), CandidateMerge.of(Type.list(v("a")), Type.list(Type.INT)));
        assertEquals(Type.list(Type.INT), CandidateMerge.of(Type.list(Type.INT), Type.list(v("a"))));
    }

    @Test
    void twoAnswersAboutWhatTheValueIsAreNotOneLeftOpen() {
        assertNull(CandidateMerge.of(Type.list(Type.INT), Type.set(Type.INT)));
        assertNull(CandidateMerge.of(Type.list(Type.INT), Type.list(Type.STRING)));
        assertNull(CandidateMerge.of(pair(Type.INT, Type.INT),
                Type.tuple(List.of(Type.INT, Type.INT, Type.INT))));
    }

    /** A variable says one thing everywhere it stands, so a second appearance meets the first. */
    @Test
    void oneVariableStandingTwiceHoldsOneType() {
        assertNull(CandidateMerge.of(pair(v("a"), v("a")), pair(Type.INT, Type.STRING)));
        assertEquals(pair(Type.INT, Type.INT),
                CandidateMerge.of(pair(v("a"), v("a")), pair(Type.INT, Type.INT)));
    }

    /** A variable's earlier reading is itself a reading, so the two are taken together rather than
     * compared: what one position said it holds answers the position that left it open. */
    @Test
    void whatAVariableStoodForAlreadyIsReadWithWhatItStandsForNow() {
        assertEquals(Type.map(Type.STRING, Type.STRING),
                CandidateMerge.of(Type.map(v("a"), v("a")), Type.map(Type.STRING, v("b"))));
        assertEquals(pair(Type.INT, Type.INT),
                CandidateMerge.of(pair(v("a"), v("a")), pair(Type.INT, v("b"))));
    }

    /** Nothing built from a value holds that value, so a reading saying so is not one to take. */
    @Test
    void aVariableDoesNotStandForSomethingHoldingItself() {
        assertNull(CandidateMerge.of(v("a"), Type.list(v("a"))));
        assertNull(CandidateMerge.of(Type.list(v("a")), v("a")));
        assertNull(CandidateMerge.of(v("a"), pair(Type.INT, v("a"))));
    }

    /**
     * What one reading said about a variable is still said when the next reading arrives. Readings
     * are taken one at a time as the walk finds them, so a relation two of them settle has to reach
     * the third: {@code a} is {@code b} and {@code b} is a list of {@code b} cannot both hold,
     * whichever pair is put together first.
     */
    @Test
    void whatTwoReadingsSettledIsStillSettledWhenTheThirdArrives() {
        assertNull(CandidateMerge.of(List.of(v("a"), v("b"), Type.list(v("b")))));
        assertNull(CandidateMerge.of(List.of(Type.list(v("b")), v("b"), v("a"))));

        Type ab = pair(v("a"), v("b"));
        Type ba = pair(v("b"), v("a"));
        Type intA = pair(Type.INT, v("a"));
        assertEquals(pair(Type.INT, Type.INT), CandidateMerge.of(List.of(ab, ba, intA)));
        assertEquals(pair(Type.INT, Type.INT), CandidateMerge.of(List.of(ab, intA, ba)));
        assertEquals(pair(Type.INT, Type.INT), CandidateMerge.of(List.of(ba, intA, ab)));
        assertEquals(pair(Type.INT, Type.INT), CandidateMerge.of(List.of(intA, ab, ba)));
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
            assertEquals(CandidateMerge.of(two[0], two[1]), CandidateMerge.of(two[1], two[0]),
                    Type.show(two[0]) + " with " + Type.show(two[1]));
        }
    }

    /** Several readings are folded pairwise, so the order they arrive in decides nothing either. */
    @Test
    void foldingThreeReadingsDoesNotDependOnTheOrderTheyArriveIn() {
        Type a = Type.list(v("a"));
        Type b = Type.list(Type.INT);
        Type c = Type.list(v("b"));
        assertEquals(CandidateMerge.of(List.of(a, b, c)), CandidateMerge.of(List.of(c, b, a)));

        Type wide = pair(v("a"), v("a"));
        Type ints = pair(Type.INT, Type.INT);
        Type mixed = pair(Type.INT, Type.STRING);
        assertNull(CandidateMerge.of(List.of(wide, ints, mixed)));
        assertNull(CandidateMerge.of(List.of(mixed, ints, wide)));
        assertNull(CandidateMerge.of(List.of(ints, mixed, wide)));
    }
}
