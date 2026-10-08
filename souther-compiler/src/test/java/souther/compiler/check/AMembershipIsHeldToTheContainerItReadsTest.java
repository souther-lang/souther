package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.CompleteSignature;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A container holding a value is some element of it being that value, and the law saying so is
 * held to the container the operation reads: the value is of the type the elements are, the
 * container is one, and what the operation answers is a truth.
 */
class AMembershipIsHeldToTheContainerItReadsTest {

    @Test
    void theOnesTheLanguageDeclaresAreHeld() {
        BoundOperationFacts facts = OperationFactBinder.bindAll(DefaultStdlib.get());
        for (String library : List.of("List", "Set")) {
            ValueName contains = ValueName.Stdlib.operation(library, "contains");
            BoundOperationFacts.Settled.ByALaw law = assertInstanceOf(
                    BoundOperationFacts.Settled.ByALaw.class,
                    facts.settled(contains, OperationLaw.Observed.TRUTH), library);
            assertTrue(law.law() instanceof OperationLaw.Observation<DeclaredArgument>(
                            var _, LawProposition.SomeElement<DeclaredArgument> _),
                    () -> library + ".contains holds a value where some element is it");
        }
    }

    /** An operation handed no container at the place the law reads one is refused. */
    @Test
    void anOperationReadingNoContainerIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bind("String.contains"));
        assertTrue(e.getMessage().contains("String.contains"), e.getMessage());
        assertTrue(e.getMessage().contains("not a container"), e.getMessage());
    }

    /** A value of another type than the elements is refused: a map's elements are its values,
     *  and `Map.containsKey` is handed a key. */
    @Test
    void aValueNoElementCanBeIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bind("Map.containsKey"));
        assertTrue(e.getMessage().contains("Map.containsKey"), e.getMessage());
        assertTrue(e.getMessage().contains("are one value"), e.getMessage());
    }

    /** And whether a container holds a value is a truth. */
    @Test
    void anOperationAnsweringNoTruthIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bind("List.take"));
        assertTrue(e.getMessage().contains("List.take"), e.getMessage());
    }

    /** That some element of argument 2 is argument 1, as {@code operation}'s truth. */
    private static void bind(String operation) {
        int dot = operation.indexOf('.');
        CompleteSignature declaration = OperationFactBinder.declaredSignature(DefaultStdlib.get(),
                ValueName.Stdlib.operation(operation.substring(0, dot),
                        operation.substring(dot + 1)));
        ArgumentRef value = new ArgumentRef.At(0);
        ArgumentRef container = new ArgumentRef.At(1);
        OperationFactBinder.holdLaw(declaration, declaration.declaring(),
                new OperationLaw.Observation<>(AnswerAspect.TRUTH,
                        new LawProposition.SomeElement<>(container, new LawProposition.Same<>(
                                new LawSubject.ElementOf<>(container),
                                new LawSubject.Argument<>(value), true), true)));
    }
}
