package souther.compiler.meta;

import souther.compiler.Compiler;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeReachName;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.lang.classfile.Annotation;
import java.lang.classfile.AnnotationElement;
import java.lang.classfile.AnnotationValue;
import java.lang.classfile.ClassFile;
import java.lang.classfile.attribute.RuntimeInvisibleAnnotationsAttribute;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior that declares stages has its signature computed, and the computed one is published as
 * source (spec {@code [#a-published-signature-is-written-in-names-its-module-has]}). So it is
 * written in the names the module publishing it has — asked of the module, never assembled from the
 * type's own identity, which says which declaration it is and not what anyone calls it.
 *
 * <p>Which leaves the case where the module has no name for it. That is refused here, at the
 * behavior whose signature it is: the alternatives are an artifact naming something a reader
 * resolves to nothing — or worse, to whatever it has under that spelling — and an artifact missing a
 * declaration it says nothing about.
 */
class APublishedSignatureIsWrittenInNamesItsModuleHasTest {

    private static final String PRICING = """
            module shop.pricing exposing ( Cart, Priced, quote )
            data Cart = { n: Int }
            data Priced = { total: Int }
            behavior quote : (c: Cart) -> Priced constructs Priced
            let quote (c) = Priced { total = c.n }
            """;

    /** One type, three modules, three spellings — and none of them is the one the type would give
     *  of itself. What differs is only what each module wrote at the top of its own file. */
    @Test
    void oneTypeIsSpelledByWhateverNameTheModulePublishingItHas() {
        assertEquals("behavior checkout : (in0: Cart) -> Done",
                computedSignature("""
                        module shop.bare exposing ( Done, checkout : Done )
                        import shop.pricing ( Cart, Priced, quote )
                        data Done = { total: Int }
                        behavior place : (p: Priced) -> Done constructs Done
                        let place (p) = Done { total = p.total }
                        behavior checkout = quote >-> place
                        """, "shop.bare.Checkout"),
                "imported bare, so bare");

        assertEquals("behavior checkout : (in0: P.Cart) -> Done",
                computedSignature("""
                        module shop.aliased exposing ( Done, checkout : Done )
                        import shop.pricing as P ( Priced, quote )
                        data Done = { total: Int }
                        behavior place : (p: Priced) -> Done constructs Done
                        let place (p) = Done { total = p.total }
                        behavior checkout = quote >-> place
                        """, "shop.aliased.Checkout"),
                "reached under the alias this module gave the module that declares it");

        assertEquals("behavior checkout : (in0: shop.pricing.Cart) -> Done",
                computedSignature("""
                        module shop.qualified exposing ( Done, checkout : Done )
                        import shop.pricing ( Priced, quote )
                        data Done = { total: Int }
                        behavior place : (p: Priced) -> Done constructs Done
                        let place (p) = Done { total = p.total }
                        behavior checkout = quote >-> place
                        """, "shop.qualified.Checkout"),
                "no bare name and no alias for it here, so the module that declares it names it");
    }

    /** And what is published resolves where it is read: the module comes back under the import lines
     *  it travelled with, so its own names mean there what they meant here. */
    @Test
    void whatIsPublishedIsReadBackAsTheSameDeclaration() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of(PRICING, """
                module shop.bare exposing ( Done, checkout : Done )
                import shop.pricing ( Cart, Priced, quote )
                data Done = { total: Int }
                behavior place : (p: Priced) -> Done constructs Done
                let place (p) = Done { total = p.total }
                behavior checkout = quote >-> place
                """));

        // A second project, holding only the classes: it reads shop.bare's declarations back and
        // types a call against them, which is the round trip the published text exists for.
        Map<String, byte[]> downstream = Compiler.compileModules(List.of("""
                module app exposing ( run )
                import shop.bare ( Done, checkout )
                import shop.pricing ( Cart )
                behavior run : (c: Cart) -> Done
                let run (c) = checkout(c)
                """), classes::get);

        assertTrue(downstream.containsKey("app.Run"),
                "app typed against what shop.bare published; got " + downstream.keySet());
    }

    /**
     * The state that does not arrive, said as one.
     *
     * <p>A computed signature is made of what its stages were declared with, and a declared
     * signature carries neither the language's own vocabulary (E1325) nor a type its module keeps to
     * itself (E1611) — so every type reaching here is one the module has a word for. There is
     * therefore no source that produces this, and none is invented for it: the naming is asked to
     * answer that way directly, which is the only way it can be reached. What it is held to is that
     * it stays a failure rather than becoming a signature published without the type, or one
     * published under a spelling nobody gave.
     */
    @Test
    void aTypeTheModuleHasNoNameForIsAFailureOfThisCompilerAndNotOfAProgram() {
        TypeSymbol hidden = TypeSymbols.declared(new TypeKey("far.a", "Hidden"));
        Type type = new Type.Ref(hidden);

        assertEquals("Hidden",
                ModuleMetadata.computed("go", type, TypeReachName.Bare::new));

        IllegalStateException said = assertThrows(IllegalStateException.class,
                () -> ModuleMetadata.computed("go", type, TypeReachName.Unnameable::new));
        assertTrue(said.getMessage().contains("go"), said.getMessage());
        assertTrue(said.getMessage().contains("far.a.Hidden"), said.getMessage());
    }

    private static String computedSignature(String module, String binaryName) {
        return computedSignature(List.of(PRICING, module), binaryName);
    }

    private static String computedSignature(List<String> modules, String binaryName) {
        Map<String, byte[]> classes = Compiler.compileModules(modules);
        byte[] bytes = classes.get(binaryName);
        assertTrue(bytes != null, binaryName + " was not generated; got " + classes.keySet());
        for (RuntimeInvisibleAnnotationsAttribute attr : ClassFile.of().parse(bytes)
                .findAttributes(java.lang.classfile.Attributes.runtimeInvisibleAnnotations())) {
            for (Annotation a : attr.annotations()) {
                if (a.className().stringValue().endsWith("SoutherBehavior;")) {
                    for (AnnotationElement e : a.elements()) {
                        if (e.name().stringValue().equals("signature")) {
                            return ((AnnotationValue.OfString) e.value()).stringValue();
                        }
                    }
                }
            }
        }
        throw new AssertionError("no published signature on " + binaryName);
    }
}
