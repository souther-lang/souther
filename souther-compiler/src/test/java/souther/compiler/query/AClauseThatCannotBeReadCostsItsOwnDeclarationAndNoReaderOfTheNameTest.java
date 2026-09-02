package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.DerivedSymbols;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A clause nobody could read is one mistake, and it is said once.
 *
 * <p>What a declaration says about itself and what a clause of it comes to are two things. A newtype
 * applied to two values is not a construction of it, and that is wrong with the clause that wrote
 * it; the declaration is still a product of this module with the fields it lists, and a reader
 * asking that is asking about the resolution.
 *
 * <p>Held across modules because that is where it costs the most. An importer reads the declaration
 * it named for its fields and for whether it is a newtype, and neither answer is any of the clause's
 * business — told the name is not declared, the importer goes on to say the value has no field to
 * read, and the author is looking at two mistakes in two files with one written.
 */
class AClauseThatCannotBeReadCostsItsOwnDeclarationAndNoReaderOfTheNameTest {

    /** `Wide` writes a clause applying a newtype to two values. Its fields say what they say. */
    private static final String LIB = """
            module lib exposing ( Amount, Wide )

            data Amount = Int

            data Wide = { n: Int }
                invariant ok = Amount(n, n) > 0
            """;

    /** And another module reads that declaration for what it declares. */
    private static final String APP = """
            module app exposing ( widthOf, Out )

            import lib ( Wide )

            data Out = { n: Int }

            behavior widthOf : (w: Wide) -> Out constructs Out
            let widthOf (w) = Out { n = w.n }
            """;

    private static Compilation compiled() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("lib.sou", LIB);
        byId.put("app.sou", APP);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
    }

    /** One mistake, in the file that wrote it. */
    @Test
    void theClauseIsTheOnlyThingWrong() {
        Compilation c = compiled();
        c.answerEverything();

        List<String> said = c.diagnostics().values().stream().flatMap(List::stream)
                .map(each -> each.diagnostic().code()).toList();

        assertEquals(List.of("E1802"), said,
                "a clause that cannot be read is one mistake, and what the declaration says about"
                        + " itself is not another");
    }

    /** And the declaration is still read, in the module that wrote it. */
    @Test
    void theDeclarationIsStillReadWhereItWasWritten() {
        Compilation c = compiled();
        c.answerEverything();
        DerivedSymbols symbols = Scopes.derived(c.db(), "lib").value();

        Hir.Def wide = symbols.declaredNode(new TypeKey("lib", "Wide"));

        assertNotNull(wide, "`Wide` is a declaration this module writes");
        assertEquals(List.of("n"),
                assertInstanceOf(Hir.Data.class, wide).fields().stream().map(Hir.Field::name)
                        .toList(),
                "and it lists the field it lists, whatever its clause came to");
    }

    /** And by the module that imported it, which asked nothing about the clause. */
    @Test
    void theImporterReadsTheDeclarationItNamed() {
        Compilation c = compiled();
        c.answerEverything();
        DerivedSymbols symbols = Scopes.derived(c.db(), "app").value();

        assertNotNull(symbols, "`app` has names of its own to mean something");

        Hir.Def wide = symbols.declaredNode(new TypeKey("lib", "Wide"));

        assertNotNull(wide, "the imported declaration is one `lib` writes");
        assertTrue(symbols.declaredByCompilation(new TypeKey("lib", "Wide")),
                "and this compilation is what declares it, not the language");
    }
}
