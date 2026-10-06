package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which argument a membership asks for is said, and held to the container the operation reads.
 *
 * <p>The value and the container are two facts about one operation, so what makes them agree is
 * asked of the two together: an operation that reads no container asks nothing of one, and a value
 * of another type than the elements is a value no element is.
 */
class AMembershipIsHeldToTheContainerItReadsTest {

    @Test
    void theOnesTheLanguageDeclaresAreHeld() {
        BoundOperationFacts facts = OperationFactBinder.bindAll(DefaultStdlib.get());
        for (String library : List.of("List", "Set")) {
            ValueName contains = ValueName.Stdlib.operation(library, "contains");
            DeclaredArgument value = facts.asksWhetherItsContainerHolds(contains);
            assertEquals(0, value.position(), () -> library + ".contains asks of its first");
            assertEquals(1, facts.readsItsContainer(contains).container().position(),
                    () -> "and reads its second: " + library);
        }
    }

    /** An operation that reads no container is asked nothing of one. */
    @Test
    void anOperationReadingNoContainerIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWith(ValueName.Stdlib.operation("List", "isEmpty"), 0));

        assertTrue(e.getMessage().contains("List.isEmpty"), e.getMessage());
        assertTrue(e.getMessage().contains("reads no container"), e.getMessage());
    }

    /** A value of another type than the elements is refused: `List.any` is handed a closure. */
    @Test
    void aValueNoElementCanBeIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWith(ValueName.Stdlib.operation("List", "any"), 0));

        assertTrue(e.getMessage().contains("List.any"), e.getMessage());
        assertTrue(e.getMessage().contains("no element is"), e.getMessage());
    }

    /** And whether a container holds a value is a truth. */
    @Test
    void anOperationAnsweringNoTruthIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWith(ValueName.Stdlib.operation("List", "length"), 0));

        assertTrue(e.getMessage().contains("List.length"), e.getMessage());
    }

    /** The binding, over the declarations the language has plus one written here. */
    private static void bindWith(ValueName operation, int value) {
        List<OperationFacts.Declared> gained = new ArrayList<>(OperationFacts.declarations());
        gained.add(new OperationFacts.Declared(operation,
                new OperationFact.AsksWhetherItsContainerHolds(new ArgumentRef.At(value))));
        OperationFactBinder.bindAll(DefaultStdlib.get(), gained);
    }
}
