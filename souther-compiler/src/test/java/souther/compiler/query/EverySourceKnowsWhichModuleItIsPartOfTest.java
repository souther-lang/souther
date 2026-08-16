package souther.compiler.query;

import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;
import souther.compiler.meta.ModulePath;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Which module a source is part of is one question with two answers behind it: the module a file
 * declares, and the module an {@code examples for} file contributes to. A reader that has a file and
 * wants to ask about the names in it needs the second as much as the first, and reading the header
 * only ever gives the first.
 */
class EverySourceKnowsWhichModuleItIsPartOfTest {

    private static final SourceId MODEL_ID = new SourceId("m.sou");
    private static final SourceId ATTACHED_ID = new SourceId("m.examples.sou");

    private static final String MODEL = """
            module m

            data D = { v: Int }
            behavior f : (d: D) -> D
            let f (d) = d
            """;

    private static final String ATTACHED = """
            examples for m

            let base = D { v = 1 }
            """;

    private static Compilation compiled() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put(MODEL_ID.value(), MODEL);
        byId.put(ATTACHED_ID.value(), ATTACHED);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
    }

    @Test
    void aSourceThatDeclaresAModuleIsPartOfIt() {
        assertEquals("m", compiled().db().ask(new Front.ModuleOf(MODEL_ID)).value());
    }

    @Test
    void anAttachedFileIsPartOfTheModuleItsRowsAreFor() {
        assertEquals("m", compiled().db().ask(new Front.ModuleOf(ATTACHED_ID)).value());
    }

    @Test
    void aSourceThisCompilationDoesNotHaveIsPartOfNothing() {
        assertNull(compiled().db().ask(new Front.ModuleOf(new SourceId("elsewhere.sou"))).value());
    }

    @Test
    void theCompilationAnswersItTheWayItAnswersTheOtherDirection() {
        Compilation c = compiled();

        assertEquals("m", c.moduleOf(ATTACHED_ID));
        assertEquals(MODEL_ID, c.sourceIdOf("m"));
    }
}
