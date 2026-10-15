package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.semantics.BuiltFrom;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Which walks the library writes answer their step on each element of what they were handed, once
 * each — the licence a reading of an element of such a walk as the step on one element stands on
 * ({@link ElementBindings#stepAnsweredOnEachElement}) — is what their bodies are proved to build.
 *
 * <p>A list's and a map's mapping answer it; a set's mapping may answer one value for two
 * elements, a filter holds the elements it kept rather than what its closure answered, and an
 * update under one key applies its closure to one value at most. Each of the six is stated to build
 * its answer from what it walks, and each statement is filed only where the body proves it, so
 * what is read here is proved and not declared.
 */
class AWalkAnswersItsStepOnEachElementOnlyWhereItsBodyIsProvedToTest {

    @Test
    void theWalksAnsweringTheirStepOnEachElementAreTheOnesProvedToBuildThat() {
        Map<ValueName, Boolean> expected = new LinkedHashMap<>();
        expected.put(ValueName.Stdlib.operation("List", "map"), true);
        expected.put(ValueName.Stdlib.operation("List", "mapIndexed"), true);
        expected.put(ValueName.Stdlib.operation("Map", "mapValues"), true);
        expected.put(ValueName.Stdlib.operation("Set", "map"), false);
        expected.put(ValueName.Stdlib.operation("List", "filter"), false);
        expected.put(ValueName.Stdlib.operation("Map", "updateIfPresent"), false);
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        Map<ValueName, Boolean> read = new LinkedHashMap<>();
        expected.keySet().forEach(operation -> {
            BuiltFrom<DeclaredArgument> built = facts.buildsItsResultFrom(operation);
            assertNotNull(built, operation + " is stated to build its answer from what it walks,"
                    + " and its body proves it");
            read.put(operation, built.mapsEachElementOf() != null);
        });
        assertEquals(expected, read);
    }
}
