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
    public PublishedClasses.Carried of(String binaryName) {
        // Outside the reading. Whatever hands the bytes over is a caller's, and a fault in it is a
        // fault: only what this class does with bytes it was given is an answer about an artifact.
        byte[] bytes = bytesOf.apply(binaryName);
        if (bytes == null) {
            return new PublishedClasses.Carried.NoSuchClass();
        }
        try {
            return new PublishedClasses.Carried.Declared(declarationsIn(bytes));
        } catch (IllegalArgumentException _) {
            // Every reading of the class file is inside this, and it has to be. Parsing one does
            // not read it: the class-file model is lazy, and a constant pool entry an annotation
            // names is checked when the annotation is asked for its class or its members. Measured
            // on a real module's bytes — of 470 single-byte corruptions, 202 refused the parse and
            // 97 more parsed and then refused an accessor. A catch around the parse alone answers
            // the first 202 and lets the other 97 end the compilation.
            return new PublishedClasses.Carried.UnreadableMetadata();
        }
    }

    /** The descriptors {@link ModuleMetadata} writes. Matched whole rather than by their last
     *  segment: a {@code SoutherData} of somebody else's package is not one of these, and reading it
     *  as one would take a stranger's annotation for a declaration of ours. */
    private static final String MODULE = "Lsouther/runtime/meta/SoutherModule;";
    private static final String DATA = "Lsouther/runtime/meta/SoutherData;";
    private static final String BEHAVIOR = "Lsouther/runtime/meta/SoutherBehavior;";

    /**
     * What one class was annotated with, read off its bytes.
     *
     * <p>Raises where the bytes are not something this compiler can read the metadata off — which
     * covers the class file being malformed and the metadata on it not being the shape this compiler
     * writes. The two are one question here: what was asked for is a declaration of ours, and an
     * annotation of our name carrying something else is no more one than a class file that will not
     * parse. Read as a default instead, a {@code @SoutherData} with no {@code value} came back as a
     * declaration whose text is empty, and the reading went on to answer {@code Ready} for it.
     */
    private static PublishedClasses.Declarations declarationsIn(byte[] bytes) {
        PublishedClasses.SoutherModuleView module = null;
        String data = null;
        String signature = null;
        Boolean injected = null;
        for (Annotation a : annotations(bytes)) {
            switch (a.className().stringValue()) {
                case MODULE -> module = moduleView(a);
                case DATA -> data = required(a, "value");
                case BEHAVIOR -> {
                    signature = required(a, "signature");
                    injected = requiredFlag(a, "injected");
                }
                default -> { }
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

    /**
     * The {@code $Module} annotation's members.
     *
     * <p>{@code compat} and {@code header} left out read as the values the reading takes for a
     * writer this compiler does not agree with — there is no boundary revision to compare and no
     * header to parse, which is what that says. The rest of the schema's defaults are its own.
     */
    private static PublishedClasses.SoutherModuleView moduleView(Annotation a) {
        return new PublishedClasses.SoutherModuleView(
                moduleInt(a, "compat", -1), moduleString(a, "compiler", ""),
                moduleString(a, "header", ""),
                strings(a, "imports"), strings(a, "types"), strings(a, "behaviors"),
                strings(a, "invariantHelpers"));
    }

    /**
     * The value written under {@code name}, or null where the writer wrote none.
     *
     * <p>Absent and wrong are different answers and are told apart by every reader below. A member
     * a writer left out is the annotation's default, which is how a reader newer than the writer
     * goes on reading what it does carry; a member written as something the schema does not declare
     * has no default to fall back to, and the annotation is not one of ours.
     */
    private static AnnotationValue member(Annotation a, String name) {
        for (AnnotationElement e : a.elements()) {
            if (e.name().stringValue().equals(name)) {
                return e.value();
            }
        }
        return null;
    }

    /** A string member the schema declares with no default: absent or otherwise is unreadable. */
    private static String required(Annotation a, String name) {
        if (member(a, name) instanceof AnnotationValue.OfString s) {
            return s.stringValue();
        }
        throw notOurs(name);
    }

    /** A boolean member the schema declares with no default. */
    private static boolean requiredFlag(Annotation a, String name) {
        if (member(a, name) instanceof AnnotationValue.OfBoolean b) {
            return b.booleanValue();
        }
        throw notOurs(name);
    }

    /**
     * A string member of {@code SoutherModule}, or {@code absent} where the writer wrote none.
     *
     * <p>The sentinel is what a writer older than this reader leaves behind, and what the reading
     * takes as a boundary the two do not share. Written as something else, it is not that: nothing
     * older wrote a header as a number, and there is no version of this schema it belongs to.
     */
    private static String moduleString(Annotation a, String name, String absent) {
        AnnotationValue value = member(a, name);
        if (value == null) {
            return absent;
        }
        if (value instanceof AnnotationValue.OfString s) {
            return s.stringValue();
        }
        throw notOurs(name);
    }

    private static int moduleInt(Annotation a, String name, int absent) {
        AnnotationValue value = member(a, name);
        if (value == null) {
            return absent;
        }
        if (value instanceof AnnotationValue.OfInt i) {
            return i.intValue();
        }
        throw notOurs(name);
    }

    /** A member the schema declares {@code default {}}: absent is empty, and anything that is not an
     *  array of strings is not this schema's. */
    private static List<String> strings(Annotation a, String name) {
        AnnotationValue value = member(a, name);
        if (value == null) {
            return List.of();
        }
        if (!(value instanceof AnnotationValue.OfArray array)) {
            throw notOurs(name);
        }
        List<String> out = new ArrayList<>();
        for (AnnotationValue v : array.values()) {
            if (!(v instanceof AnnotationValue.OfString s)) {
                throw notOurs(name);
            }
            out.add(s.stringValue());
        }
        return out;
    }

    /** Raised for metadata of this compiler's name that is not this compiler's shape. Caught where
     *  the bytes are read, and answered as {@link PublishedClasses.Carried.UnreadableMetadata}. */
    private static IllegalArgumentException notOurs(String member) {
        return new IllegalArgumentException(
                "`" + member + "` is not what this compiler writes there");
    }
}
