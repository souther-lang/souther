package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.KeptCalls;
import souther.compiler.core.Kernel;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The positions {@link StringPredicates} names are positions the operations it is about have.
 *
 * <p>The table says a predicate of this kind takes two arguments, that the second names the
 * position a rule is about and the first carries what the author wrote. Its readers then take those
 * numbers to a call and read the arguments there. A call has the arguments its own declaration takes
 * — that is the node's — so what is left is whether these numbers are ones such a declaration has,
 * and nothing about a call says it.
 *
 * <p>Asked of the library once rather than at each call. Where the two disagree there is nothing to
 * be done at a call: every rule written with the operation is being read at the wrong position, or
 * at one that is not there, and which call happened to arrive first is no part of the answer.
 */
class WhichArgumentsAStringPredicateNamesAreOnesItsDeclarationHasTest {

    @Test
    void everyPredicateNamesOneOperationTheLibraryDeclares() {
        for (StringPredicates predicate : StringPredicates.values()) {
            assertEquals(1, declaring(predicate.kernel()).size(),
                    predicate + " is about the operations " + declaring(predicate.kernel())
                            + ", and a rule about it is read off one declaration");
        }
    }

    @Test
    void andThereAreSomeToSayThatOf() {
        assertFalse(declaring().isEmpty(), "the table is empty, so the rules below saw nothing");
    }

    @Test
    void aPredicateTakesWhatItsDeclarationTakes() {
        declaring().forEach((predicate, operation) -> assertEquals(predicate.arity(),
                KeptCalls.signature(operation).params().size(),
                operation.qualified() + " is read as a call of " + predicate.arity()
                        + " arguments"));
    }

    @Test
    void theSubjectAndTheWrittenArgumentAreTwoOfThem() {
        declaring().forEach((predicate, operation) -> {
            int params = KeptCalls.signature(operation).params().size();
            assertTrue(predicate.subject() >= 0 && predicate.subject() < params,
                    operation.qualified() + " is read for its subject at argument "
                            + (predicate.subject() + 1) + " of " + params);
            assertTrue(predicate.written() >= 0 && predicate.written() < params,
                    operation.qualified() + " is read for what was written at argument "
                            + (predicate.written() + 1) + " of " + params);
            assertNotEquals(predicate.subject(), predicate.written(),
                    operation.qualified() + " is read for both at one argument");
        });
    }

    /**
     * Which library operation each predicate is about, for the ones the library declares exactly
     * one of. What the rules below are asked over, once the test above has said that is all of
     * them.
     */
    private static Map<StringPredicates, ValueName.Stdlib.Operation> declaring() {
        Map<StringPredicates, ValueName.Stdlib.Operation> out = new LinkedHashMap<>();
        for (StringPredicates predicate : StringPredicates.values()) {
            List<ValueName.Stdlib.Operation> declared = declaring(predicate.kernel());
            if (declared.size() == 1) {
                out.put(predicate, declared.get(0));
            }
        }
        return out;
    }

    /**
     * Every operation the library declares to be {@code kernel}.
     *
     * <p>All of them and not the first: a rule here is read off a declaration, so two operations
     * declared as one kernel is two declarations for one rule to be about, and answering with
     * whichever came first would be this test choosing between them.
     */
    private static List<ValueName.Stdlib.Operation> declaring(Kernel kernel) {
        Stdlib stdlib = DefaultStdlib.get();
        Symbols symbols = Symbols.none(stdlib);
        List<ValueName.Stdlib.Operation> found = new ArrayList<>();
        for (ValueName.Stdlib.Operation each : stdlib.entries().keySet()) {
            if (symbols.kernelOf(each) == kernel) {
                found.add(each);
            }
        }
        return found;
    }
}
