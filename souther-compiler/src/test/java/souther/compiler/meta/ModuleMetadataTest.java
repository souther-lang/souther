package souther.compiler.meta;

import souther.compiler.Compiler;

import org.junit.jupiter.api.Test;

import java.lang.classfile.Annotation;
import java.lang.classfile.AnnotationElement;
import java.lang.classfile.AnnotationValue;
import java.lang.classfile.ClassFile;
import java.lang.classfile.attribute.RuntimeInvisibleAnnotationsAttribute;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A compiled module carries what it declares, so another project can import it from a jar with no
 * {@code .sou} of its own. Each definition rides on the class it generated, as the source that
 * declared it; the module's own facts ride on a {@code $Module} class emitted for them.
 */
class ModuleMetadataTest {

    private static final String UP = """
            module shared.money exposing ( Amount, charge )
            import String ( length )

            // what a payment is worth
            data Amount = Int
                invariant value >= 0 && withinCap(value)

            data Receipt = { paid: Amount }
            data Declined

            behavior charge : (a: Amount) -> Receipt | Declined
                constructs Receipt, Declined
            let charge (a) = if a.value > 0 then Receipt { paid = a } else Declined

            let withinCap (n: Int) = n <= 1000000
            let unrelated (n: Int) = n + 1
            """;

    @Test
    void aDataCarriesTheDeclarationThatDeclaredIt() {
        Map<String, byte[]> classes = Compiler.compile(UP);

        assertEquals("""
                // what a payment is worth
                data Amount = Int
                    invariant value >= 0 && withinCap(value)""",
                string(annotation(classes, "shared.money.Amount", "SoutherData"), "value"));
    }

    @Test
    void aBehaviorCarriesItsSignatureAndWhetherItIsInjected() {
        Map<String, byte[]> classes = Compiler.compile(UP);

        Annotation charge = annotation(classes, "shared.money.Charge", "SoutherBehavior");
        assertEquals("""
                behavior charge : (a: Amount) -> Receipt | Declined
                    constructs Receipt, Declined""", string(charge, "signature"));
        assertFalse(bool(charge, "injected"), "charge has a let, so nothing injects it");
    }

    @Test
    void aBehaviorWithNoLetIsMarkedInjected() {
        Map<String, byte[]> classes = Compiler.compile("""
                module shared.ledger exposing ( Entry, record )
                data Entry = { amount: Int }
                behavior record : (e: Entry) -> Entry
                """);

        assertTrue(bool(annotation(classes, "shared.ledger.Record", "SoutherBehavior"), "injected"));
    }

    @Test
    void theModuleClassNamesWhatToRead() {
        Map<String, byte[]> classes = Compiler.compile(UP);

        Annotation module = annotation(classes, "shared.money.$Module", "SoutherModule");
        assertEquals("shared.money", string(module, "name"));
        assertEquals(ModuleMetadata.COMPAT, integer(module, "compat"));
        assertEquals(List.of("Amount", "charge"), strings(module, "exposing"));
        assertEquals(List.of("Amount", "Receipt", "Declined"), strings(module, "types"));
        assertEquals(List.of("charge"), strings(module, "behaviors"));
        assertEquals(List.of("import String ( length )"), strings(module, "imports"));
    }

    /** An invariant is part of what the type is, so the helpers it calls travel with it. A helper no
     * invariant reaches is the module's own business and stays behind. */
    @Test
    void onlyTheHelpersAnInvariantReachesAreCarried() {
        Map<String, byte[]> classes = Compiler.compile(UP);

        assertEquals(List.of("let withinCap (n: Int) = n <= 1000000"),
                strings(annotation(classes, "shared.money.$Module", "SoutherModule"),
                        "invariantHelpers"));
    }

    /** A composition declares stages, not a signature. The importing module reads a signature, so
     * the computed one is written out and the stages stay behind. */
    @Test
    void aCompositionPublishesTheSignatureItComputesTo() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module shop.pricing exposing ( Cart, Priced, quote )
                data Cart = { n: Int }
                data Priced = { total: Int }
                behavior quote : (c: Cart) -> Priced constructs Priced
                let quote (c) = Priced { total = c.n }
                """, """
                module shop.checkout exposing ( Done, place, checkout : Done )
                import shop.pricing ( Cart, Priced, quote )
                data Done = { total: Int }
                behavior place : (p: Priced) -> Done constructs Done
                let place (p) = Done { total = p.total }
                behavior checkout = quote >-> place
                """));

        assertEquals("behavior checkout : (in0: shop.pricing.Cart) -> shop.checkout.Done",
                string(annotation(classes, "shop.checkout.Checkout", "SoutherBehavior"), "signature"));
    }

    private static Annotation annotation(Map<String, byte[]> classes, String binaryName,
                                         String simpleAnnotationName) {
        byte[] bytes = classes.get(binaryName);
        assertTrue(bytes != null, binaryName + " was not generated; got " + classes.keySet());
        for (RuntimeInvisibleAnnotationsAttribute attr : ClassFile.of().parse(bytes)
                .findAttributes(java.lang.classfile.Attributes.runtimeInvisibleAnnotations())) {
            for (Annotation a : attr.annotations()) {
                if (a.className().stringValue().endsWith("/" + simpleAnnotationName + ";")) {
                    return a;
                }
            }
        }
        throw new AssertionError(binaryName + " carries no @" + simpleAnnotationName);
    }

    private static AnnotationValue member(Annotation a, String name) {
        for (AnnotationElement e : a.elements()) {
            if (e.name().stringValue().equals(name)) {
                return e.value();
            }
        }
        throw new AssertionError("no member `" + name + "`");
    }

    private static String string(Annotation a, String name) {
        return ((AnnotationValue.OfString) member(a, name)).stringValue();
    }

    private static boolean bool(Annotation a, String name) {
        return ((AnnotationValue.OfBoolean) member(a, name)).booleanValue();
    }

    private static int integer(Annotation a, String name) {
        return ((AnnotationValue.OfInt) member(a, name)).intValue();
    }

    private static List<String> strings(Annotation a, String name) {
        List<String> out = new ArrayList<>();
        for (AnnotationValue v : ((AnnotationValue.OfArray) member(a, name)).values()) {
            out.add(((AnnotationValue.OfString) v).stringValue());
        }
        return out;
    }
}
