package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior's output union is built from its own module's cases (E1606, ADR-0057). The reason is
 * not the JVM's same-package rule for {@code permits} — that one is javac's, and only when it
 * declares a sealed type in source (issue #95). It is that a case class receives the unions it
 * belongs to when its own module is generated, so a class an imported module already emitted cannot
 * implement an interface declared here.
 */
class CompileCrossModuleUnionTest {

    private static final String INVENTORY = """
            module inv exposing ( Sku, Allocated, Shortage, allocate )
            data Sku = String
            data Allocated = { sku: Sku }
            data Shortage = { sku: Sku }
            behavior allocate : (sku: Sku) -> Allocated | Shortage
                constructs Allocated, Shortage
            """;

    @Test
    void aCaseClassCarriesOnlyItsOwnModulesUnions() throws Exception {
        // the fact the rule rests on: `implements` is settled here, when `inv` is generated
        Map<String, byte[]> classes = Compiler.compileModules(List.of(INVENTORY));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> shortage = loader.loadClass("inv.Shortage");
        assertEquals(List.of(loader.loadClass("inv.AllocateResult")),
                Arrays.asList(shortage.getInterfaces()),
                "a case class implements the unions of its own module and no others");
    }

    @Test
    void aDepartedImportedCaseIsRejected() {
        String shipping = """
                module ship
                import inv ( Sku, Allocated, Shortage, allocate )
                data Shipped = { sku: Sku }
                behavior instruct : (a: Allocated) -> Shipped
                    constructs Shipped
                let instruct (a) = Shipped { sku = a.sku }
                behavior allocateAndShip = allocate >-> instruct
                """;
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(INVENTORY, shipping)));
        assertEquals("E1606", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("Shortage"), e.getMessage());
        assertFalse(e.getMessage().contains("permit"),
                "the reason is module generation order, not the `permits` rule: " + e.getMessage());
    }

    @Test
    void anImportedCaseDeclaredInAnOutputIsRejectedToo() {
        // not only a `>->` departure: writing the imported case in the declared output is the same
        String shipping = """
                module ship
                import inv ( Sku, Allocated, Shortage, allocate )
                data Shipped = { sku: Sku }
                behavior ship : (sku: Sku) -> Shipped | Shortage
                    requires allocate
                    constructs Shipped
                let ship (sku, allocate) =
                    match allocate(sku) with
                    | Allocated as a -> Shipped { sku = a.sku }
                    | Shortage as s -> s
                """;
        assertEquals("E1606", assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(INVENTORY, shipping))).code());
    }

    @Test
    void translatingTheImportedCaseIntoOneOfThisModuleCompilesAndRuns() throws Exception {
        // the move the diagnostic asks for: restate the other context's case in this module's terms
        String shipping = """
                module ship
                import inv ( Sku, Allocated, Shortage, allocate )
                data Shipped = { sku: Sku }
                data NotShipped = { sku: Sku }
                behavior ship : (sku: Sku) -> Shipped | NotShipped
                    requires allocate
                    constructs Shipped, NotShipped
                let ship (sku, allocate) =
                    match allocate(sku) with
                    | Allocated as a -> Shipped { sku = a.sku }
                    | Shortage as s -> NotShipped { sku = s.sku }
                """;
        Map<String, byte[]> classes = Compiler.compileModules(List.of(INVENTORY, shipping));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> union = loader.loadClass("ship.ShipResult");
        assertEquals(List.of(loader.loadClass("ship.NotShipped"), loader.loadClass("ship.Shipped")),
                Arrays.asList(union.getPermittedSubclasses()),
                "the union is this module's cases, and each of them implements it");
        assertTrue(union.isAssignableFrom(loader.loadClass("ship.NotShipped")));
    }
}
