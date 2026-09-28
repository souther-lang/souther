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

    /** Whether the type has an order, which is {@link Ordering#of} having an answer. */
    private static boolean ordered(Type type) {
        return Ordering.of(type, NewtypeInners.NONE, null, DeclarationKinds.NONE,
                PublishedDeclarations.NONE) != null;
    }

    @Test
    void aTupleComparesButDoesNotOrder() {
        Type pair = Type.tuple(List.of(Type.STRING, Type.STRING));
        assertTrue(TypeOps.supportsEquality(pair));
        assertFalse(ordered(pair));
    }

    @Test
    void aFunctionAnswersNoneOfTheThree() {
        Type fn = Type.fn(List.of(Type.INT), Type.BOOL);
        assertFalse(TypeOps.supportsEquality(fn));
        assertFalse(ordered(fn));
        assertFalse(TypeOps.hasExternalForm(fn, null));
    }

    @Test
    void aCollectionOfFunctionsCannotBeCompared() {
        Type fn = Type.fn(List.of(Type.INT), Type.BOOL);
        assertFalse(TypeOps.supportsEquality(Type.list(fn)));
        assertFalse(TypeOps.supportsEquality(Type.set(fn)));
        assertFalse(TypeOps.supportsEquality(Type.option(fn)));
        assertFalse(TypeOps.supportsEquality(Type.map(Type.STRING, fn)));
        assertFalse(TypeOps.supportsEquality(Type.tuple(List.of(Type.INT, fn))));
    }

    @Test
    void aListOfOrderedElementsIsNotItselfOrdered() {
        assertFalse(ordered(Type.list(Type.INT)));
        assertTrue(TypeOps.supportsEquality(Type.list(Type.INT)));
    }

    @Test
    void theOrderedPrimitivesAreTheFiveThatCarryAnOrder() {
        assertTrue(ordered(Type.INT));
        assertTrue(ordered(Type.STRING));
        assertTrue(ordered(Type.DECIMAL));
        assertTrue(ordered(Type.DATE));
        assertTrue(ordered(Type.DATETIME));
    }

    @Test
    void boolComparesButDoesNotOrder() {
        assertTrue(TypeOps.supportsEquality(Type.BOOL));
        assertFalse(ordered(Type.BOOL));
    }

    @Test
    void onlyAFunctionIsRefusedAnExternalForm() {
        assertTrue(TypeOps.hasExternalForm(Type.list(Type.STRING), null));
        assertTrue(TypeOps.hasExternalForm(Type.map(Type.STRING, Type.DECIMAL), null));
        assertFalse(TypeOps.hasExternalForm(Type.list(Type.fn(List.of(), Type.INT)), null));
    }
}
