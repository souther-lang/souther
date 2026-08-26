package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a {@code fake} and a {@code with} stand in for is a behavior, settled by resolving the name.
 *
 * <p>A stand-in used to carry the spelling an author wrote and be matched against a requirement by
 * it. A requirement is a behavior — the module that declares it and its name — so the two only
 * agreed while every dependency was declared in the module its rows were written in. Across a module
 * boundary they came apart in both directions: a table written for the dependency answered nothing,
 * and one written for a namesake declared here answered in its place (issue #1108).
 *
 * <p>So a name written here is read the way a behavior is read anywhere else, and what the compiler
 * carries from there on is the behavior and not the characters.
 */
class AStandInNamesTheBehaviorItStandsInForTest {

    private static final String CATALOG = """
            module probe.catalog exposing ( Sku, Stock, currentStock )

            data Sku = String
            data Stock = { sku: Sku, count: Int }

            behavior currentStock : (sku: Sku) -> Stock
            """;

    /**
     * The borrowing module: {@code brings} is what its import line takes bare, and {@code body} is
     * written after its own declarations.
     */
    private static String shipping(String brings, String body) {
        return """
                module probe.shipping exposing ( Shipped )
                import probe.catalog as Catalog ( Sku, Stock%s )

                data Shipped = { sku: Sku, count: Int }""".formatted(brings) + """


                behavior ship : (sku: Sku) -> Shipped
                    constructs Shipped
                    depends on Catalog.currentStock

                let ship (sku, currentStock) = {
                    let s = currentStock(sku)
                    Shipped { sku = sku, count = s.count }
                }

                let 在庫あり = Stock { sku = Sku("a-1"), count = 3 }

                example ship
                    | "one" : (Sku("a-1")) -> Shipped { sku = Sku("a-1"), count = 3 }
                """ + body;
    }

    private static List<String> codesOf(String brings, String body) {
        List<String> codes = new java.util.ArrayList<>();
        Compilation compiled = Compilation.ofSources(List.of(CATALOG, shipping(brings, body)),
                ModulePath.EMPTY);
        compiled.answerEverything();
        compiled.errors().forEach(e -> codes.add(e.diagnostic().code()));
        return codes;
    }

    /**
     * A requirement declared in one module and carried through another's {@code depends on} is
     * stood in for where that module's rows are run.
     *
     * <p>The construct the conformance corpus was missing, and the one the whole of this is about:
     * the row runs, so the stand-in reached the behavior the clause named.
     */
    @Test
    void aRequirementCarriedAcrossAModuleBoundaryIsStoodInFor() {
        assertEquals(List.of(), codesOf(", currentStock", """

                fake currentStock
                    | _ -> 在庫あり
                """), "a fake for the borrowed dependency answers it");
    }

    /**
     * And it may be named through the module that declares it, as a {@code depends on} may.
     *
     * <p>Written with no import bringing the bare spelling in, so the qualified name is the whole of
     * what reaches the behavior.
     */
    @Test
    void theStandInMayNameTheDependencyThroughItsModule() {
        assertEquals(List.of(), codesOf("", """

                fake Catalog.currentStock
                    | _ -> 在庫あり
                """), "the qualified spelling names the same behavior");
    }

    /**
     * A namesake declared here is a different behavior, and standing in for it does not answer the
     * borrowed requirement.
     *
     * <p>What used to happen is worth saying, because it is why the identity is carried: the local
     * behavior's table was installed in the borrowed dependency's place, its fixture was built
     * against the local signature, and the row aborted casting one module's value to another's —
     * reported as the row not holding, which is a statement about the model.
     */
    @Test
    void aNamesakeDeclaredHereDoesNotAnswerTheBorrowedRequirement() {
        List<String> codes = codesOf("", """

                behavior currentStock : (sku: Sku) -> Shipped

                fake currentStock
                    | _ -> Shipped { sku = Sku("a-1"), count = 3 }
                """);

        assertEquals(List.of("E1908"), codes,
                "the borrowed dependency is the one nothing stands in for");
    }

    /** A name no behavior answers to is refused where it is written, rather than leaving a table
     *  nothing could ever read. */
    @Test
    void aStandInNamingNoBehaviorIsRefused() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile("""
                module example.nothing

                data N = Int

                behavior use : (n: N) -> N
                let use (n) = n

                fake findNothing
                    | _ -> N(1)
                """));

        assertEquals("E1932", refused.code(), refused.getMessage());
        assertTrue(refused.getMessage().contains("findNothing"),
                "the name that answers to nothing is the one quoted: " + refused.getMessage());
    }

    /** The same for a {@code with} on a row, which names a dependency the same way. */
    @Test
    void aWithNamingNoBehaviorIsRefused() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile("""
                module example.nothingonrow

                data N = Int

                behavior use : (n: N) -> N
                let use (n) = n

                example use
                    | "one" : (N(1)) with findNothing = N(2) -> N(1)
                """));

        assertEquals("E1932", refused.code(), refused.getMessage());
    }
}
