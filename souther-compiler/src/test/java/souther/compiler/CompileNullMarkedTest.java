package souther.compiler;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.classfile.attribute.RuntimeVisibleAnnotationsAttribute;
import java.lang.classfile.attribute.SignatureAttribute;
import java.lang.constant.ClassDesc;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Nothing generated is ever null: absence is {@code Option}, a failure is a case of the output union.
 * A consumer that reads nullness from the bytecode cannot know that unless the classes say so, and a
 * Kotlin caller that is told nothing falls back to platform types, where a null check is neither
 * required nor possible. So every generated class carries JSpecify's {@code @NullMarked}.
 */
class CompileNullMarkedTest {

    private static final ClassDesc NULL_MARKED = ClassDesc.of("org.jspecify.annotations.NullMarked");

    private static final String SRC = """
            module demo
            data Amount = Int
            data Receipt = { paid: Amount }
            behavior charge : (a: Amount) -> Receipt
                constructs Receipt
            let charge (a) = Receipt { paid = a }
            """;

    @Test
    void everyGeneratedClassIsMarked() {
        // the whole runtime-visible list, not just that the marking is among it: what a generated
        // class states to a consumer's compiler is the boundary, and a second annotation arriving
        // there is a decision to take rather than something to let through. The module's declarations
        // ride on `$Module` as runtime-invisible for that reason.
        Map<String, byte[]> classes = Compiler.compile(SRC);

        assertTrue(classes.size() > 1, "there is more than one class to mark: " + classes.keySet());
        for (Map.Entry<String, byte[]> e : classes.entrySet()) {
            assertEquals(List.of(NULL_MARKED), annotations(e.getValue()), e.getKey());
        }
    }

    @Test
    void noPackageInfoIsEmitted() {
        // a module's package is where a consumer's own package-info.java lives; the marking rides on
        // the classes so that declaration has nothing to collide with (issue #150)
        Set<String> emitted = Compiler.compile(SRC).keySet();

        assertTrue(emitted.stream().noneMatch(n -> n.endsWith(".package-info")),
                "no package annotations are generated: " + emitted);
    }

    @Test
    void eachModuleOfALinkedSetMarksItsOwnClasses() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module shared.money exposing ( Amount )
                data Amount = Int
                """, """
                module ordering
                import shared.money ( Amount )
                data Line = { paid: Amount }
                """));

        assertEquals(List.of(NULL_MARKED), annotations(classes.get("shared.money.Amount")));
        assertEquals(List.of(NULL_MARKED), annotations(classes.get("ordering.Line")));
    }

    @Test
    void constructHandsBackATypedResult() {
        // `__construct` is public for an exposed type and is the path another module's `constructs`
        // takes; a raw `Result` there is a platform type again to a Kotlin caller
        assertEquals("(Ldemo/Amount;)Lsouther/runtime/Result<Ldemo/Receipt;Ljava/lang/String;>;",
                methodSignature(Compiler.compile(SRC).get("demo.Receipt"), "__construct"));
    }

    /** The annotation types the class carries as runtime-visible — what a Kotlin compiler reads. */
    private static List<ClassDesc> annotations(byte[] bytes) {
        return ClassFile.of().parse(bytes).findAttribute(java.lang.classfile.Attributes
                        .runtimeVisibleAnnotations())
                .map(RuntimeVisibleAnnotationsAttribute::annotations).orElse(List.of())
                .stream().map(a -> a.classSymbol()).toList();
    }

    /** The generic {@code Signature} of the named method, or null where it has none. */
    private static String methodSignature(byte[] bytes, String method) {
        return ClassFile.of().parse(bytes).methods().stream()
                .filter(m -> m.methodName().stringValue().equals(method))
                .findFirst().orElseThrow()
                .findAttribute(java.lang.classfile.Attributes.signature())
                .map(SignatureAttribute::signature).map(s -> s.stringValue()).orElse(null);
    }
}
