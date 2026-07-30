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
                    depends on allocate
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
                    depends on allocate
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

    @Test
    void anOperationSpanningTwoModulesIsOneBehavior() throws Exception {
        // What a cross-module `>->` would have been: the imported stage runs, its departure is
        // answered with a case declared here, and its mainline goes on to a stage of this module —
        // one that has a requirement of its own, so it is received rather than built (ADR-0068).
        String inventory = INVENTORY + """
                let allocate (sku) =
                    if String.length(sku.value) > 0 then Allocated { sku = sku } else Shortage { sku = sku }
                """;
        String shipping = """
                module ship
                import inv ( Sku, Allocated, Shortage, allocate )
                data Label = { text: String }
                data Shipped = { sku: Sku, label: Label }
                data NoLabel
                data NotAllocated = { sku: Sku }
                behavior printLabel : (sku: Sku) -> Label
                    constructs Label
                behavior instruct : (a: Allocated) -> Shipped | NoLabel
                    depends on printLabel
                    constructs Shipped, NoLabel
                let instruct (a, printLabel) =
                    if String.length(a.sku.value) > 0
                    then Shipped { sku = a.sku, label = printLabel(a.sku) }
                    else NoLabel
                behavior allocateAndShip : (sku: Sku) -> Shipped | NoLabel | NotAllocated
                    depends on instruct
                    constructs NotAllocated
                let allocateAndShip (sku, instruct) =
                    match allocate(sku) with
                    | Allocated as a -> instruct(a)
                    | Shortage as s -> NotAllocated { sku = s.sku }
                """;
        Map<String, byte[]> classes = Compiler.compileModules(List.of(inventory, shipping));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Class<?> union = loader.loadClass("ship.AllocateAndShipResult");
        assertEquals(List.of(loader.loadClass("ship.NoLabel"), loader.loadClass("ship.NotAllocated"),
                        loader.loadClass("ship.Shipped")),
                Arrays.asList(union.getPermittedSubclasses()),
                "both stages' outcomes reach one union, all of them declared here");
        // a stage this module implements is received, so the boundary binds it rather than its leaves
        assertEquals(List.of(loader.loadClass("ship.Instruct")),
                Arrays.asList(loader.loadClass("ship.AllocateAndShip")
                        .getMethod("bind", loader.loadClass("ship.Instruct")).getParameterTypes()));
    }

    @Test
    void anImportedBehaviorOfSeveralArgumentsIsCalledOnItsOwnResultUnion() throws Exception {
        // A one-input behavior is reached through the erased `Behavior.apply`, so nothing names its
        // result union. Any other arity is called on a typed `apply` that does, and the union belongs
        // to the module that declared the behavior — not to the one reading it.
        String inventory = """
                module inv exposing ( Sku, Allocated, Shortage, allocateFor )
                data Sku = String
                data Allocated = { sku: Sku }
                data Shortage = { sku: Sku }
                behavior allocateFor : (sku: Sku, qty: Int) -> Allocated | Shortage
                    constructs Allocated, Shortage
                let allocateFor (sku, qty) =
                    if qty > 0 then Allocated { sku = sku } else Shortage { sku = sku }
                """;
        String shipping = """
                module ship exposing ( Shipped, NotAllocated, ship )
                import inv ( Sku, Allocated, Shortage, allocateFor )
                data Shipped = { sku: Sku }
                data NotAllocated = { sku: Sku }
                behavior ship : (sku: Sku, qty: Int) -> Shipped | NotAllocated
                    constructs Shipped, NotAllocated
                let ship (sku, qty) =
                    match allocateFor(sku, qty) with
                    | Allocated as a -> Shipped { sku = a.sku }
                    | Shortage as s -> NotAllocated { sku = s.sku }
                """;
        Map<String, byte[]> classes = Compiler.compileModules(List.of(inventory, shipping));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Object behavior = loader.loadClass("ship.Ship$Impl").getConstructor().newInstance();
        Object sku = Codecs.decoded(loader, "inv.Sku", "SKU-1");
        assertEquals("ship.Shipped", applyTwo(behavior, sku, 3L).getClass().getName(),
                "the call links because the union it names is inv's");
        assertEquals("ship.NotAllocated", applyTwo(behavior, sku, 0L).getClass().getName());
    }

    /** Apply a reflectively-instantiated two-argument behavior. */
    private static Object applyTwo(Object behavior, Object a, Object b) throws Exception {
        for (java.lang.reflect.Method m : behavior.getClass().getDeclaredMethods()) {
            if (m.getName().equals("apply") && m.getParameterCount() == 2) {
                return m.invoke(behavior, a, b);
            }
        }
        throw new AssertionError("no two-argument apply on " + behavior.getClass());
    }
}
