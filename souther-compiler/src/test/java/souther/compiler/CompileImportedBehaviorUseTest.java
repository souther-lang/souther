package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.jvm.ClassFileImage;

import org.junit.jupiter.api.Test;

import javax.tools.ToolProvider;

import java.io.File;
import java.nio.file.Files;
import java.util.HashMap;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An imported behavior can be named where a local one can: as a {@code >->} stage and as a {@code depends on}
 * dependency (spec §modules, §injected-behavior, §composition-with-requirements). The declaring module's
 * arity is what decides how it is called, not whether it crossed a module boundary — a multi-input injected
 * behavior is injected and called on its base class either way (issue #96, issue #57).
 */
class CompileImportedBehaviorUseTest {

    private static final String INVENTORY = """
            module probe.inventory exposing ( Sku, Quantity, Allocated, allocate )

            data Sku = String
            data Quantity = Int
            data Allocated = { sku: Sku, quantity: Quantity }

            behavior allocate : (sku: Sku, quantity: Quantity) -> Allocated
                constructs Allocated
            """;

    private static final String ALLOCATE_IMPL = """
            package probe.inventory;
            public final class AllocateImpl extends Allocate {
                public Allocated apply(Sku sku, Quantity quantity) {
                    return Allocated(sku, quantity);
                }
            }
            """;

    @Test
    void anImportedMultiInputInjectedBehaviorStartsAPipeline() throws Exception {
        // issue #96: the stage resolved to no signature at all, so it was reported as a missing name
        String shipping = """
                module probe.shipping
                import probe.inventory ( Sku, Quantity, Allocated, allocate )

                data Shipped = { sku: Sku }

                behavior instruct : (a: Allocated) -> Shipped
                    constructs Shipped
                let instruct (a) = Shipped { sku = a.sku }

                behavior allocateAndShip = allocate >-> instruct
                """;
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(INVENTORY, shipping));
        assertTrue(classes.containsKey(Emitted.impl("probe.shipping", "allocateAndShip")),
                "the pipeline is generated: " + classes.keySet());
    }

    @Test
    void anImportedMultiInputInjectedFirstStageIsBoundAndRuns() throws Exception {
        String shipping = """
                module probe.shipping
                import probe.inventory ( Sku, Quantity, Allocated, allocate )

                data Shipped = { sku: Sku, quantity: Quantity }

                behavior instruct : (a: Allocated) -> Shipped
                    constructs Shipped
                let instruct (a) = Shipped { sku = a.sku, quantity = a.quantity }

                behavior allocateAndShip = allocate >-> instruct
                """;
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compileModules(List.of(INVENTORY, shipping)));
        classes.put("probe.inventory.AllocateImpl",
                compileSubclass(classes, "probe.inventory.AllocateImpl", ALLOCATE_IMPL));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());

        Class<?> base = loader.loadClass("probe.inventory.Allocate");
        Object pipeline = loader.loadClass("probe.shipping.AllocateAndShip").getMethod("bind", base)
                .invoke(null, loader.loadClass("probe.inventory.AllocateImpl").getConstructor().newInstance());
        Object sku = Codecs.decoded(loader, "probe.inventory.Sku", "S-1");
        Object quantity = Codecs.decoded(loader, "probe.inventory.Quantity", 3L);
        Object shipped = pipeline.getClass()
                .getMethod("apply", loader.loadClass("probe.inventory.Sku"),
                        loader.loadClass("probe.inventory.Quantity"))
                .invoke(pipeline, sku, quantity);

        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "probe.shipping.Shipped", shipped);
        assertEquals("S-1", out.get("sku"));
        assertEquals(3L, out.get("quantity"), "both of the imported stage's arguments reach it");
    }

    @Test
    void anImportedInjectedBehaviorIsARequiresDependencyAndRuns() throws Exception {
        // issue #96: `depends on` never saw imported behaviors, so the call fell through to E1401,
        // which told the author to declare a behavior they had already declared and imported.
        String shipping = """
                module probe.shipping
                import probe.inventory ( Sku, Quantity, Allocated, allocate )

                data Shipped = { sku: Sku, quantity: Quantity }

                behavior ship : (sku: Sku, quantity: Quantity) -> Shipped
                    depends on allocate
                    constructs Shipped
                let ship (sku, quantity, allocate) = {
                    let a = allocate(sku, quantity)
                    Shipped { sku = a.sku, quantity = a.quantity }
                }
                """;
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compileModules(List.of(INVENTORY, shipping)));
        classes.put("probe.inventory.AllocateImpl",
                compileSubclass(classes, "probe.inventory.AllocateImpl", ALLOCATE_IMPL));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());

        Class<?> base = loader.loadClass("probe.inventory.Allocate");
        Object ship = loader.loadClass("probe.shipping.Ship").getMethod("bind", base)
                .invoke(null, loader.loadClass("probe.inventory.AllocateImpl").getConstructor().newInstance());
        Object sku = Codecs.decoded(loader, "probe.inventory.Sku", "S-2");
        Object quantity = Codecs.decoded(loader, "probe.inventory.Quantity", 7L);
        Object shipped = ship.getClass()
                .getMethod("apply", loader.loadClass("probe.inventory.Sku"),
                        loader.loadClass("probe.inventory.Quantity"))
                .invoke(ship, sku, quantity);

        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "probe.shipping.Shipped", shipped);
        assertEquals("S-2", out.get("sku"));
        assertEquals(7L, out.get("quantity"));
    }

    @Test
    void aSingleInputImportedInjectedBehaviorIsARequiresDependency() {
        String inventory = """
                module probe.inv1 exposing ( Sku, Allocated, allocate )
                data Sku = String
                data Allocated = { sku: Sku }
                behavior allocate : (sku: Sku) -> Allocated
                    constructs Allocated
                """;
        String shipping = """
                module probe.ship1
                import probe.inv1 ( Sku, Allocated, allocate )
                data Shipped = { sku: Sku }
                behavior ship : (sku: Sku) -> Shipped
                    depends on allocate
                    constructs Shipped
                let ship (sku, allocate) = {
                    let a = allocate(sku)
                    Shipped { sku = a.sku }
                }
                """;
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(inventory, shipping));
        assertTrue(classes.containsKey(Emitted.impl("probe.ship1", "ship")), classes.keySet().toString());
    }

    @Test
    void anImportedMultiInputBehaviorCannotFollowAnArrow() {
        // `>->` hands one value along, so the rule is the same for an imported stage as a local one —
        // and it is the rule the author is told, not that the name could not be found
        String shipping = """
                module probe.ship4
                import probe.inventory ( Sku, Quantity, Allocated, allocate )
                data Shipped = { sku: Sku }
                behavior pick : (sku: Sku) -> Sku
                let pick (sku) = sku
                behavior pickAndAllocate = pick >-> allocate
                """;
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(INVENTORY, shipping)));
        assertTrue(e.getMessage().contains("`allocate` takes 2 inputs"), e.getMessage());
    }

    @Test
    void anImportedCaseInTheOutputUnionReachesItFromEitherPosition() throws Exception {
        // Both of issue #96's reproductions keep an imported case in the consuming behavior's own
        // output union: one reaches it as a `>->` departure, the other from a body that matched the
        // dependency's result. The two roads produce the same union, bridged the same way.
        String inventory = """
                module probe.inv2 exposing ( Sku, Allocated, Shortage, allocate )
                data Sku = String
                data Allocated = { sku: Sku }
                data Shortage = { sku: Sku }
                behavior allocate : (sku: Sku, quantity: Int) -> Allocated | Shortage
                """;
        String asAStage = """
                module probe.ship2
                import probe.inv2 ( Sku, Allocated, Shortage, allocate )
                data Shipped = { sku: Sku }
                behavior instruct : (a: Allocated) -> Shipped
                    constructs Shipped
                let instruct (a) = Shipped { sku = a.sku }
                behavior allocateAndShip = allocate >-> instruct
                """;
        String asADependency = """
                module probe.ship3
                import probe.inv2 ( Sku, Allocated, Shortage, allocate )
                data Shipped = { sku: Sku }
                behavior ship : (sku: Sku, quantity: Int) -> Shipped | Shortage
                    depends on allocate
                    constructs Shipped
                let ship (sku, quantity, allocate) =
                    match allocate(sku, quantity) with
                    | Allocated as a -> Shipped { sku = a.sku }
                    | Shortage as s -> s
                """;
        for (String consumer : List.of(asAStage, asADependency)) {
            Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(inventory, consumer));
            String pkg = consumer == asAStage ? "probe.ship2" : "probe.ship3";
            String result = consumer == asAStage ? "AllocateAndShipResult" : "ShipResult";
            BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
            assertEquals(List.of(loader.loadClass(pkg + ".Shipped"),
                            loader.loadClass(pkg + ".ShortageCase")),
                    Arrays.asList(loader.loadClass(pkg + "." + result).getPermittedSubclasses()),
                    "the imported case is bridged, this module's own case is itself");
        }
    }

    /** Compiles {@code source} against the generated classes and returns the class bytes. */
    private static ClassFileImage compileSubclass(Map<String, ClassFileImage> generated,
                                                  String className, String source)
            throws Exception {
        java.nio.file.Path classesDir = Files.createTempDirectory("souther-gen");
        for (Map.Entry<String, ClassFileImage> e : generated.entrySet()) {
            java.nio.file.Path p = classesDir.resolve(e.getKey().replace('.', '/') + ".class");
            Files.createDirectories(p.getParent());
            Files.write(p, e.getValue().bytes());
        }
        java.nio.file.Path srcFile = classesDir.resolve(className.replace('.', '/') + ".java");
        Files.writeString(srcFile, source);
        java.nio.file.Path outDir = Files.createTempDirectory("souther-impl");
        String cp = classesDir + File.pathSeparator + System.getProperty("java.class.path");
        int rc = ToolProvider.getSystemJavaCompiler().run(null, null, null,
                "-encoding", "UTF-8", "-classpath", cp, "-d", outDir.toString(), srcFile.toString());
        if (rc != 0) {
            throw new IllegalStateException("javac failed for " + className + " (rc=" + rc + ")");
        }
        return ClassFileImage.of(
                Files.readAllBytes(outDir.resolve(className.replace('.', '/') + ".class")));
    }
}
