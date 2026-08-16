package souther.compiler.query;

import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A definition exists where its meaning was settled, and the unit that is settled is the
 * declaration.
 *
 * <p>Two ways there is none. A name written in it was not answered, so what it is made of is not
 * there; or what it reaches has no meaning, so what it is made of is not there either. The second
 * is not "a diagnostic was reported upstream" and not "the module will not be emitted" — either of
 * those would put the question of what a name means back in the hands of a later check. It is that
 * the declaration this one reaches did not come out, which is a fact about the declaration and is
 * settled where the declaration is.
 *
 * <p>The declaration beside them is untouched. Taking a whole module away over one unknown name
 * would take away every answer the compiler had about the rest of it, and an author fixing a
 * misspelt type would be told about the next mistake only after the compile that follows.
 */
class ADefinitionReachingOneThatWasNotBuiltIsNotBuiltTest {

    private static Compilation compiled(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", source);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
    }

    private static boolean has(Compilation c, String declared) {
        return c.db().ask(new Names.Definition(new TypeKey("m.a", declared))).present();
    }

    /** `Line` reaches `Order`, which names nothing. */
    @Test
    void aDeclarationReachingAnUnbuiltOneIsNotBuiltAndTheIndependentOneIs() {
        Compilation c = compiled("""
                module m.a exposing ( Order, Line, Note )

                data Order = { total: Nowhere }
                data Line = { order: Order }
                data Note = { text: String }
                """);

        assertFalse(has(c, "Order"), "`Nowhere` was not answered");
        assertFalse(has(c, "Line"), "what `Line` is made of has no meaning, so neither has `Line`");
        assertTrue(has(c, "Note"), "and a declaration reaching neither is untouched");
    }

    /** The same where what is reached is written after what reaches it. */
    @Test
    void whereTheUnbuiltDeclarationIsWrittenLaterItStillTakesTheOneThatReachesIt() {
        Compilation c = compiled("""
                module m.a exposing ( Early, Late )

                data Early = { o: Late }
                data Late = { x: Nowhere }
                """);

        assertFalse(has(c, "Late"), "`Nowhere` was not answered");
        assertFalse(has(c, "Early"), "which the declaration above it is made of");
    }

    /**
     * And nothing is said about one of these a second time. The author has one mistake and is told
     * about it once; a report against the declaration that merely reaches it sends them to a line
     * that is correct — here, that `Order` has no decoder, which is not a second mistake but the
     * first one said again from further downstream.
     */
    @Test
    void theOneMistakeIsReportedOnceAndNotAgainstWhatReachesIt() {
        Compilation c = compiled("""
                module m.a exposing ( Order, Line )

                data Order = { total: Nowhere }
                data Line = { order: Order }
                """);
        List<String> said = Located.diagnosticsOf(c.diagnostics()).get(new SourceId("a.sou")).stream()
                .map(d -> d.code() + " " + d.said()).toList();

        assertEquals(1, said.size(), "the unknown name, and nothing about `Line`: " + said);
    }

}
