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
import static org.junit.jupiter.api.Assertions.assertNotNull;
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
    void everyPredicateNamesAnOperationTheLibraryDeclares() {
        assertEquals(List.of(), unmatched(), "no library operation is declared to be this kernel");
    }

    @Test
    void andThereAreSomeToSayThatOf() {
        assertFalse(StringPredicates.values().length == 0, "the table is empty");
        assertEquals(StringPredicates.values().length, declaring().size(),
                "each predicate is matched to the one operation declared to be its kernel");
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

    /** Which library operation each predicate is about, by the kernel it is declared to be. */
    private static Map<StringPredicates, ValueName.Stdlib.Operation> declaring() {
        Map<StringPredicates, ValueName.Stdlib.Operation> out = new LinkedHashMap<>();
        for (StringPredicates predicate : StringPredicates.values()) {
            ValueName.Stdlib.Operation declared = declaring(predicate.kernel());
            if (declared != null) {
                out.put(predicate, declared);
            }
        }
        return out;
    }

    private static List<StringPredicates> unmatched() {
        List<StringPredicates> out = new ArrayList<>();
        for (StringPredicates predicate : StringPredicates.values()) {
            if (declaring(predicate.kernel()) == null) {
                out.add(predicate);
            }
        }
        return out;
    }

    /** The one operation the library declares to be {@code kernel}. */
    private static ValueName.Stdlib.Operation declaring(Kernel kernel) {
        Stdlib stdlib = DefaultStdlib.get();
        Symbols symbols = Symbols.none(stdlib);
        ValueName.Stdlib.Operation found = null;
        for (ValueName.Stdlib.Operation each : stdlib.entries().keySet()) {
            if (symbols.kernelOf(each) == kernel) {
                assertNotNull(each);
                found = found == null ? each : found;
            }
        }
        return found;
    }
}
