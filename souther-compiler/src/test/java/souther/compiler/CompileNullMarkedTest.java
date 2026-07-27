package souther.compiler;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.attribute.RuntimeVisibleAnnotationsAttribute;
import java.lang.constant.ClassDesc;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Nothing generated is ever null: absence is {@code Option}, a failure is a case of the output union.
 * A consumer that reads nullness from the bytecode cannot know that unless the classes say so, and a
 * Kotlin caller that is told nothing falls back to platform types, where a null check is neither
 * required nor possible. So each generated package carries JSpecify's {@code @NullMarked}.
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
    void aModuleCarriesNullMarkedOnItsPackage() {
        Map<String, byte[]> classes = Compiler.compile(SRC);

        byte[] bytes = classes.get("demo.package-info");
        assertTrue(bytes != null, "the module's package is marked: " + classes.keySet());
        assertEquals(List.of(NULL_MARKED), annotations(bytes));
    }

    @Test
    void thePackageInfoIsShapedAsJavacWouldEmitOne() {
        ClassModel model = ClassFile.of().parse(Compiler.compile(SRC).get("demo.package-info"));

        assertEquals(ClassFile.ACC_INTERFACE | ClassFile.ACC_ABSTRACT | ClassFile.ACC_SYNTHETIC,
                model.flags().flagsMask(), "an interface, abstract and synthetic, as javac emits");
        assertTrue(model.methods().isEmpty() && model.fields().isEmpty(), "it declares nothing");
    }

    @Test
    void eachModuleOfALinkedSetMarksItsOwnPackage() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module shared.money exposing ( Amount )
                data Amount = Int
                """, """
                module ordering
                import shared.money ( Amount )
                data Line = { paid: Amount }
                """));

        assertEquals(List.of(NULL_MARKED), annotations(classes.get("shared.money.package-info")));
        assertEquals(List.of(NULL_MARKED), annotations(classes.get("ordering.package-info")));
    }

    /** The annotation types the class carries as runtime-visible — what a Kotlin compiler reads. */
    private static List<ClassDesc> annotations(byte[] bytes) {
        return ClassFile.of().parse(bytes).findAttribute(java.lang.classfile.Attributes
                        .runtimeVisibleAnnotations())
                .map(RuntimeVisibleAnnotationsAttribute::annotations).orElse(List.of())
                .stream().map(a -> a.classSymbol()).toList();
    }
}
