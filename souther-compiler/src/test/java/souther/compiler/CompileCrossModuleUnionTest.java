package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.reflect.Proxy;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
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

        // The stage is *received*: this counting stand-in is what runs, not something the composed
        // behavior built for itself. A `bind` parameter of the right type would say nothing about that.
        Object shipped = Codecs.decoded(loader, "ship.Shipped",
                Map.of("sku", "SKU-1", "label", Map.of("text", "L")));
        int[] calls = new int[1];
        Object instruct = Proxy.newProxyInstance(loader, new Class<?>[] {loader.loadClass("ship.Instruct")},
                (proxy, method, args) -> {
                    if (!method.getName().equals("apply")) {
                        return method.getName().equals("toString") ? "instruct" : Boolean.FALSE;
                    }
                    calls[0]++;
                    return shipped;
                });
        Object composed = loader.loadClass("ship.AllocateAndShip")
                .getMethod("bind", loader.loadClass("ship.Instruct")).invoke(null, instruct);

        assertSame(shipped, Codecs.apply(composed, Codecs.decoded(loader, "inv.Sku", "SKU-1")),
                "the mainline reaches the received stage and its answer is the answer");
        assertEquals(1, calls[0]);

        // The imported departure never reaches the next stage; it is answered here instead.
        Object refused = Codecs.apply(composed, Codecs.decoded(loader, "inv.Sku", ""));
        assertEquals("ship.NotAllocated", refused.getClass().getName());
        assertEquals(1, calls[0], "a departed case does not go on to the next stage");
    }

    @Test
    void anImportedBehaviorOfNoArgumentsIsCalledOnItsOwnResultUnion() throws Exception {
        // The other half of "not one argument", and it reaches the typed `apply` by a different road:
        // a behavior of no arguments cannot have a body at all (a `let` with no parameter list is a
        // value, ADR-0072), so it is always injected and reached through `depends on`.
        String issuing = """
                module up exposing ( Token, NoToken, mint )
                data Token = { v: String }
                data NoToken
                behavior mint : () -> Token | NoToken
                    constructs Token, NoToken
                """;
        String stamping = """
                module down exposing ( Stamped, Unstamped, stamp )
                import up ( Token, NoToken, mint )
                data Stamped = { v: String }
                data Unstamped
                behavior stamp : (n: Int) -> Stamped | Unstamped
                    depends on mint
                    constructs Stamped, Unstamped
                let stamp (n, mint) =
                    match mint() with
                    | Token as t -> Stamped { v = t.v }
                    | NoToken -> Unstamped
                """;
        Map<String, byte[]> classes = Compiler.compileModules(List.of(issuing, stamping));
        // The call is not run here: `up.Mint` is an abstract class with a protected constructor, so a
        // stand-in cannot be made by reflection alone. What the bug produced was a descriptor naming a
        // class nothing emits, which is what is checked — the call linked to `down.MintResult` before.
        assertEquals("()Lup/MintResult;", calleeDescriptor(classes.get("down.Stamp$Impl"), "up/Mint"));
        assertTrue(classes.containsKey("up.MintResult"), "and that class is one this compilation wrote");
    }

    /** The descriptor {@code $Impl} calls {@code apply} with on {@code owner}, read off the bytes. */
    private static String calleeDescriptor(byte[] impl, String owner) {
        for (MethodModel m : ClassFile.of().parse(impl).methods()) {
            for (CodeElement e : m.code().orElseThrow()) {
                if (e instanceof InvokeInstruction call
                        && call.owner().asInternalName().equals(owner)
                        && call.name().stringValue().equals("apply")) {
                    return call.type().stringValue();
                }
            }
        }
        throw new AssertionError("no call to " + owner + ".apply");
    }

    @Test
    void anImportedBehaviorOfTwoArgumentsIsCalledOnItsOwnResultUnion() throws Exception {
        // A one-input behavior is reached through the erased `Behavior.apply`, so nothing names its
        // result union. Any other arity — this one and the no-argument one below — is called on a
        // typed `apply` that does, and the union belongs to the module that declared the behavior,
        // not to the one reading it.
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
