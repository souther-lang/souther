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
        return codesOf(brings, body, "");
    }

    /** The same, {@code catalogRows} written after the catalog's own declarations. */
    private static List<String> codesOf(String brings, String body, String catalogRows) {
        List<String> codes = new java.util.ArrayList<>();
        Compilation compiled = Compilation.ofSources(
                List.of(CATALOG + "\n" + catalogRows, shipping(brings, body)), ModulePath.EMPTY);
        compiled.answerEverything();
        compiled.errors().forEach(e -> codes.add(e.diagnostic().code()));
        compiled.warnings().forEach(w -> codes.add(w.diagnostic().code()));
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

    /**
     * A stand-in here and the rows recorded where the behavior is declared are read against each
     * other.
     *
     * <p>Two written statements about one behavior, and after this change they need not be in one
     * module: a row records what a behavior owes where the behavior is declared, and a table stands
     * in for it where the rows that run against it are. Read only within a module, the comparison
     * would pass over every pair this change made writable — which is the state the corpus itself
     * turned out to be in.
     */
    @Test
    void aStandInIsReadAgainstTheRowsRecordedWhereTheBehaviorIsDeclared() {
        List<String> codes = codesOf(", currentStock", """

                fake currentStock
                    | (Sku("z-9")) -> Stock { sku = Sku("z-9"), count = 9 }
                    | _            -> 在庫あり
                """, """
                example currentStock
                    | "the odd one is down to three" : (Sku("z-9"))
                        -> Stock { sku = Sku("z-9"), count = 3 }
                """);

        assertEquals(List.of("E1919"), codes,
                "the table says nine and the catalog's own row says three");
    }

    /** And where the two say the same thing, nothing is said. */
    @Test
    void aStandInThatAgreesWithThoseRowsSaysNothing() {
        assertEquals(List.of(), codesOf(", currentStock", """

                fake currentStock
                    | (Sku("z-9")) -> Stock { sku = Sku("z-9"), count = 3 }
                    | _            -> 在庫あり
                """, """
                example currentStock
                    | "the odd one is down to three" : (Sku("z-9"))
                        -> Stock { sku = Sku("z-9"), count = 3 }
                """));
    }

    /**
     * A {@code with} is read against the declaring module's rows as a {@code fake} is.
     *
     * <p>Its own claim because it is written without a table, and what says which modules a reading
     * takes the rows of is what this module writes stand-ins for. Asked of the tables instead — the
     * question of which table answers for a dependency — a row that supplies one with a {@code with}
     * and writes no table names a module the reading never reads, and the two statements are
     * compared against nothing.
     */
    @Test
    void aWithForABorrowedDependencyIsReadAgainstThoseRowsToo() {
        List<String> codes = new java.util.ArrayList<>();
        Compilation compiled = Compilation.ofSources(List.of("""
                module probe.clocks exposing ( Stamp, now )

                data Stamp = String

                behavior now : () -> Stamp

                example now
                    | "the hour it is" : () -> Stamp("09:00")
                """, """
                module probe.filing exposing ( Filed )
                import probe.clocks as Clocks ( Stamp )

                data Filed = { at: Stamp }

                behavior file : (at: Stamp) -> Filed
                    constructs Filed
                    depends on Clocks.now

                let file (at, now) = Filed { at = now() }

                example file
                    | "filed at the hour" : (Stamp("x"))
                        with Clocks.now = Stamp("10:00") -> Filed { at = Stamp("10:00") }
                """), ModulePath.EMPTY);
        compiled.answerEverything();
        compiled.errors().forEach(e -> codes.add(e.diagnostic().code()));
        compiled.warnings().forEach(w -> codes.add(w.diagnostic().code()));

        assertEquals(List.of("E1919"), codes,
                "the `with` says ten and the clock's own row says nine");
    }

    /**
     * A borrowed dependency taking more than one input is stood in for too.
     *
     * <p>Its own claim because it is its own path. A dependency taking one input is injected as a
     * {@code Behavior} proxy, which names no module; any other count is a generated subclass of the
     * abstract base the declaring module emitted (spec §java-base-class, ADR-0056), and which module
     * that is has to be read off the behavior. Read off the module being applied instead, the
     * subclass names a class nothing generated — and every unary stand-in goes on working, which is
     * how the reading that found this defect found the arity mattered.
     */
    @Test
    void aBorrowedDependencyTakingSeveralInputsIsStoodInFor() {
        List<String> codes = new java.util.ArrayList<>();
        Compilation compiled = Compilation.ofSources(List.of("""
                module probe.warehouses exposing ( Sku, Bay, Stock, stockAt )

                data Sku = String
                data Bay = String
                data Stock = { sku: Sku, count: Int }

                behavior stockAt : (sku: Sku, bay: Bay) -> Stock
                    constructs Stock
                """, """
                module probe.picking exposing ( Picked )
                import probe.warehouses as Warehouses ( Sku, Bay, Stock, stockAt )

                data Picked = { sku: Sku, count: Int }

                behavior pick : (sku: Sku, bay: Bay) -> Picked
                    constructs Picked
                    depends on stockAt

                let pick (sku, bay, stockAt) = {
                    let s = stockAt(sku, bay)
                    Picked { sku = sku, count = s.count }
                }

                fake Warehouses.stockAt
                    | (Sku("a-1"), Bay("b-1")) -> Stock { sku = Sku("a-1"), count = 4 }
                    | _                        -> Stock { sku = Sku("a-1"), count = 0 }

                example pick
                    | "what the named bay holds" : (Sku("a-1"), Bay("b-1"))
                        -> Picked { sku = Sku("a-1"), count = 4 }
                    | "and nothing anywhere else" : (Sku("a-1"), Bay("b-9"))
                        -> Picked { sku = Sku("a-1"), count = 0 }
                """), ModulePath.EMPTY);
        compiled.answerEverything();
        compiled.errors().forEach(e -> codes.add(e.diagnostic().code()));

        assertEquals(List.of(), codes, "both rows run against the two-input borrowed dependency");
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
