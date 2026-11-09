package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That an operation agrees with another where it is given a string is held to both declarations:
 * it takes a string at that place, and the arguments that remain and what it answers are what the
 * other takes and answers, so a call of the first is a call of the second.
 */
class AnOperationAgreeingWithAnotherWhereItIsGivenTextIsHeldToBothSignaturesTest {

    private static final ValueName JOIN = ValueName.Stdlib.operation("String", "join");
    private static final ValueName CONCAT = ValueName.Stdlib.operation("String", "concat");

    /** Control: what the library declares is bound, and is read by the one place that rewrites. */
    @Test
    void joiningWithNothingAgreesWithPuttingEndToEnd() {
        BoundOperationFact.AgreesWithAnotherWhereItIsGivenText agrees =
                DefaultBoundOperationFacts.get().agreesWhereItIsGivenText(JOIN);

        assertEquals(CONCAT, agrees.other().operation());
        assertEquals(0, agrees.position());
        assertEquals("", agrees.text());
    }

    /** An operation taking no string at the place is not one a string is given to. */
    @Test
    void anOperationTakingNoStringThereAgreesWithNothingGivenOne() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bind(ValueName.Stdlib.operation("List", "length"), 0, CONCAT));
        assertTrue(e.getMessage().contains("List.length"), e.getMessage());
    }

    /** What remains of the arguments has to be what the other takes. */
    @Test
    void anOperationWhoseRemainingArgumentsAreNotTheOthersAgreesWithNothing() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bind(JOIN, 0, ValueName.Stdlib.operation("String", "length")));
        assertTrue(e.getMessage().contains("String.join"), e.getMessage());
    }

    private static void bind(ValueName operation, int position, ValueName other) {
        List<OperationFacts.Declared> declared = new ArrayList<>(OperationFacts.declarations());
        declared.add(new OperationFacts.Declared(operation,
                new OperationFact.AgreesWithAnotherWhereItIsGivenText(other, position, "")));
        OperationFactBinder.bindAll(DefaultStdlib.get(), declared);
    }
}
