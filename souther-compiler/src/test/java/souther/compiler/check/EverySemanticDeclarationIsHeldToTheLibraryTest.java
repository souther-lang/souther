package souther.compiler.check;

import org.junit.jupiter.api.Test;

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
 * Every fact declared of the language's operations is held to what the library declares, whether or
 * not anything asks for it.
 *
 * <p>The declarations and the procedure that holds them to the library are in different places now:
 * a fact is a proposition about an operation and is declared where those are, and holding one to a
 * signature reads the library, which is the frontend's. What that arrangement can lose is the
 * reaching — bound one fact at a time as it was looked up, a fact nothing looked up was a fact
 * nothing checked, and how much of the declaration was validated depended on which consumers a
 * compilation happened to have.
 *
 * <p>So what is asked here is coverage of the declarations and not of the lookups. A test naming
 * the facts that exist today would be a second copy of the list, wrong in the same way one turn
 * later; these are asked of the source, so a fact declared tomorrow is inside them without anyone
 * adding a line.
 */
class EverySemanticDeclarationIsHeldToTheLibraryTest {

    /** Everything the language declares is visited, and the visiting is over the declarations. */
    @Test
    void theBindingIsOverTheDeclarations() {
        assertEquals(OperationFacts.declarations(),
                OperationFactBinder.bindAll(OperationFacts.declarations()),
                "what the binding visited is what is declared");
        assertTrue(!OperationFacts.declarations().isEmpty(),
                "and there is something declared for that to mean anything");
    }

    /**
     * A fact the source gains is held too, without the binding being told about it.
     *
     * <p>The whole of the contract, and the part the assertion above cannot show on its own: a
     * binding that walked a list of its own would visit exactly what is declared today and nothing
     * that arrives later. So one is added here that the library refuses, and the binding is asked
     * whether it noticed.
     */
    @Test
    void aFactTheDeclarationsGainIsHeldWithoutTheBindingBeingTold() {
        List<OperationFacts.Declared> gained =
                new ArrayList<>(OperationFacts.declarations());
        gained.add(new OperationFacts.Declared(
                new ValueName.Stdlib("Decimal", "fromInt"),
                new OperationFact.AnswersItsArgument(new ArgumentRef.At(7))));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(gained));

        assertTrue(refused.getMessage().contains("Decimal.fromInt"), refused.getMessage());
        assertTrue(refused.getMessage().contains("argument 8"),
                "the argument the added fact names, which the operation does not take: "
                        + refused.getMessage());
    }

    /**
     * And a fact about an operation the library does not declare at all.
     *
     * <p>Beside the above because it fails one question earlier: there is no signature to read the
     * argument against, so what is wrong is the operation and not the argument.
     */
    @Test
    void aFactAboutAnOperationTheLibraryDoesNotDeclareIsRefused() {
        List<OperationFacts.Declared> gained =
                new ArrayList<>(OperationFacts.declarations());
        gained.add(new OperationFacts.Declared(
                new ValueName.Stdlib("Decimal", "fromNothingAtAll"),
                new OperationFact.AnswersItsArgument(new ArgumentRef.At(0))));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(gained));

        assertTrue(refused.getMessage().contains("the library does not declare"),
                refused.getMessage());
    }
}
