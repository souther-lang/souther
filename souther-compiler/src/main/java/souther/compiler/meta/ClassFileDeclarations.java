package souther.compiler.meta;

import java.lang.classfile.Annotation;
import java.lang.classfile.AnnotationElement;
import java.lang.classfile.AnnotationValue;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

/**
 * Reads what {@link ModuleMetadata} wrote, out of class files.
 *
 * <p>This is the reader for anywhere the bytes are in hand — the classes of a compile in progress,
 * a jar entry. Under an annotation processor the same annotations are reachable through
 * {@code Elements} without the bytes, which is a second reader of the same shape.
 */
public final class ClassFileDeclarations implements PublishedClasses {

    private final Function<String, byte[]> bytesOf;

    /** Reads from whatever {@code bytesOf} returns for a binary class name; null for absent. */
    public ClassFileDeclarations(Function<String, byte[]> bytesOf) {
        this.bytesOf = bytesOf;
    }

    @Override
    public PublishedClasses.Declarations of(String binaryName) {
        byte[] bytes = bytesOf.apply(binaryName);
        if (bytes == null) {
            return null;
        }
        PublishedClasses.SoutherModuleView module = null;
        String data = null;
        String signature = null;
        Boolean injected = null;
        for (Annotation a : annotations(bytes)) {
            String type = a.className().stringValue();
            if (type.endsWith("/SoutherModule;")) {
                module = moduleView(a);
            } else if (type.endsWith("/SoutherData;")) {
                data = string(a, "value");
            } else if (type.endsWith("/SoutherBehavior;")) {
                signature = string(a, "signature");
                injected = bool(a, "injected");
            }
        }
        return new PublishedClasses.Declarations(module, data, signature, injected);
    }

    private static List<Annotation> annotations(byte[] bytes) {
        return ClassFile.of().parse(bytes)
                .findAttribute(Attributes.runtimeInvisibleAnnotations())
                .map(a -> List.copyOf(a.annotations()))
                .orElse(List.of());
    }

    private static PublishedClasses.SoutherModuleView moduleView(Annotation a) {
        return new PublishedClasses.SoutherModuleView(
                integer(a, "compat"), string(a, "compiler"), string(a, "name"), string(a, "header"),
                strings(a, "imports"), strings(a, "types"), strings(a, "behaviors"),
                strings(a, "invariantHelpers"));
    }

    /** An absent member means the writer left it at its default, which for every member here is
     * empty; a reader older than the writer sees the same thing. */
    private static AnnotationValue member(Annotation a, String name) {
        for (AnnotationElement e : a.elements()) {
            if (e.name().stringValue().equals(name)) {
                return e.value();
            }
        }
        return null;
    }

    private static String string(Annotation a, String name) {
        return member(a, name) instanceof AnnotationValue.OfString s ? s.stringValue() : "";
    }

    private static boolean bool(Annotation a, String name) {
        return member(a, name) instanceof AnnotationValue.OfBoolean b && b.booleanValue();
    }

    private static int integer(Annotation a, String name) {
        return member(a, name) instanceof AnnotationValue.OfInt i ? i.intValue() : -1;
    }

    private static List<String> strings(Annotation a, String name) {
        List<String> out = new ArrayList<>();
        if (member(a, name) instanceof AnnotationValue.OfArray array) {
            for (AnnotationValue v : array.values()) {
                if (v instanceof AnnotationValue.OfString s) {
                    out.add(s.stringValue());
                }
            }
        }
        return out;
    }
}
