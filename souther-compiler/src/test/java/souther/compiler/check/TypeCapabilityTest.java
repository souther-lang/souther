package souther.compiler.check;

import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The three capability questions are answered per type constructor in one place. They are three
 * questions, not one: equality and the external form descend into what a collection holds, and an
 * ordering does not, because a collection has none of its own whatever it holds.
 */
class TypeCapabilityTest {

    @Test
    void aTupleComparesButDoesNotOrder() {
        Type pair = Type.tuple(List.of(Type.STRING, Type.STRING));
        assertTrue(TypeOps.supportsEquality(pair, null));
        assertFalse(TypeOps.supportsOrdering(pair, null));
    }

    @Test
    void aFunctionAnswersNoneOfTheThree() {
        Type fn = Type.fn(List.of(Type.INT), Type.BOOL);
        assertFalse(TypeOps.supportsEquality(fn, null));
        assertFalse(TypeOps.supportsOrdering(fn, null));
        assertFalse(TypeOps.hasExternalForm(fn, null));
    }

    @Test
    void aCollectionOfFunctionsCannotBeCompared() {
        Type fn = Type.fn(List.of(Type.INT), Type.BOOL);
        assertFalse(TypeOps.supportsEquality(Type.list(fn), null));
        assertFalse(TypeOps.supportsEquality(Type.set(fn), null));
        assertFalse(TypeOps.supportsEquality(Type.option(fn), null));
        assertFalse(TypeOps.supportsEquality(Type.map(Type.STRING, fn), null));
        assertFalse(TypeOps.supportsEquality(Type.tuple(List.of(Type.INT, fn)), null));
    }

    @Test
    void aListOfOrderedElementsIsNotItselfOrdered() {
        assertFalse(TypeOps.supportsOrdering(Type.list(Type.INT), null));
        assertTrue(TypeOps.supportsEquality(Type.list(Type.INT), null));
    }

    @Test
    void theOrderedPrimitivesAreTheFiveThatCarryAnOrder() {
        assertTrue(TypeOps.supportsOrdering(Type.INT, null));
        assertTrue(TypeOps.supportsOrdering(Type.STRING, null));
        assertTrue(TypeOps.supportsOrdering(Type.DECIMAL, null));
        assertTrue(TypeOps.supportsOrdering(Type.DATE, null));
        assertTrue(TypeOps.supportsOrdering(Type.DATETIME, null));
    }

    @Test
    void boolAndRawCompareButDoNotOrder() {
        assertTrue(TypeOps.supportsEquality(Type.BOOL, null));
        assertFalse(TypeOps.supportsOrdering(Type.BOOL, null));
        assertTrue(TypeOps.supportsEquality(Type.RAW, null));
        assertFalse(TypeOps.supportsOrdering(Type.RAW, null));
    }

    @Test
    void onlyAFunctionIsRefusedAnExternalForm() {
        assertTrue(TypeOps.hasExternalForm(Type.list(Type.STRING), null));
        assertTrue(TypeOps.hasExternalForm(Type.map(Type.STRING, Type.DECIMAL), null));
        assertFalse(TypeOps.hasExternalForm(Type.list(Type.fn(List.of(), Type.INT)), null));
    }
}
