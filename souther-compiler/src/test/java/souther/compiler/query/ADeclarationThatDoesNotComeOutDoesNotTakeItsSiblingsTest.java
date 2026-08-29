package souther.compiler.query;

import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a declaration comes to is answered for that declaration.
 *
 * <p>{@link Shapes.DerivedDef} says of itself that a reader depends on the declaration it named and
 * not on everything declared beside it. The work behind it was a module at a time all the same, and
 * one clause that could not be read took the answer away from every declaration in the file — a
 * reader asking about a type written above the mistake, and reaching nothing to do with it, was told
 * there is no such type.
 *
 * <p>So the failure is owned where it happened. The declaration that wrote the clause has no
 * answer; the ones beside it have theirs. The module is assembled from all of them and is there only
 * when each one is, which is a different question and is asked once.
 */
class ADeclarationThatDoesNotComeOutDoesNotTakeItsSiblingsTest {

    /** `Bad` applies a newtype to two values, which is not something a newtype wraps. */
    private static final String SOURCE = """
            module m.a exposing ( Amount, Bad, Note )

            data Amount = Int

            data Bad = Int
                invariant ok = Amount(value, value) > 0

            data Note = { text: String }
            """;

    private static Compilation compiled() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", SOURCE);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
    }

    private static boolean derived(Compilation c, String declared) {
        return c.db().ask(new Shapes.DerivedDef(new TypeKey("m.a", declared))).present();
    }

    @Test
    void theDeclarationWithTheMistakeHasNoAnswerAndTheOthersHaveTheirs() {
        Compilation c = compiled();

        assertFalse(derived(c, "Bad"), "the clause it wrote cannot be read");
        assertTrue(derived(c, "Amount"), "which is nothing to do with what `Amount` is");
        assertTrue(derived(c, "Note"), "nor with what `Note` is");
    }

    /** And the module, which is every one of them, is not there. */
    @Test
    void theModuleIsNotAssembledWhileOneOfItsDeclarationsIsMissing() {
        assertFalse(compiled().db().ask(new Shapes.Derived("m.a")).present());
    }

    /** The mistake is said once, where it is written. */
    @Test
    void theOneMistakeIsSaidOnce() {
        List<String> said = Located.diagnosticsOf(compiled().diagnostics()).get(new SourceId("a.sou")).stream()
                .map(d -> d.code() + " " + d.said()).toList();

        assertEquals(1, said.size(), said.toString());
        assertTrue(said.get(0).startsWith("E1802"), said.toString());
    }
}
