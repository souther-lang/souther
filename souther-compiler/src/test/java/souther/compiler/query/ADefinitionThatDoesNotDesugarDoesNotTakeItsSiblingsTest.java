package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.meta.ModulePath;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a definition's body comes to is answered for that definition.
 *
 * <p>The same proposition as {@link ADeclarationThatDoesNotComeOutDoesNotTakeItsSiblingsTest}, one
 * stage down and about a different unit: a declaration is what the stage above answers for, and a
 * definition is what this one answers for. An application that wraps no single value is wrong in the
 * body that wrote it, and the definition beside it is written about something else.
 */
class ADefinitionThatDoesNotDesugarDoesNotTakeItsSiblingsTest {

    /** `f` applies a newtype to two values; `g` is written about nothing to do with it. */
    private static final String SOURCE = """
            module m.a exposing ( Amount, f, g )

            data Amount = Int

            behavior f : (n: Int) -> Int
            let f (n) = Amount(n, n).value

            behavior g : (n: Int) -> Int
            let g (n) = n
            """;

    private static Compilation compiled() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", SOURCE);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
    }

    @Test
    void theDefinitionWithTheMistakeHasNoAnswerAndTheOneBesideItHasOne() {
        Compilation c = compiled();

        assertFalse(c.db().ask(new Shapes.DesugaredFn("m.a", "f")).present(),
                "what `f` wrote is not an application of a newtype");
        assertTrue(c.db().ask(new Shapes.DesugaredFn("m.a", "g")).present(),
                "which is nothing to do with what `g` is");
    }

    /** And the module, which is every one of them, is not there. */
    @Test
    void theModuleIsNotAssembledWhileOneOfItsDefinitionsIsMissing() {
        assertFalse(compiled().db().ask(new Shapes.Desugared("m.a")).present());
    }
}
