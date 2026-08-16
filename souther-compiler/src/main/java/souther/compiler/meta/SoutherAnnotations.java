package souther.compiler.meta;

import java.lang.classfile.Annotation;
import java.lang.classfile.AnnotationElement;
import java.lang.classfile.AnnotationValue;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.util.ArrayList;
import java.util.List;

/**
 * Reads the annotations {@link ModuleMetadata} writes, off the bytes of one class.
 *
 * <p>The only thing in this package that reads a class file. Reading one and reading the metadata on
 * it are both here, because both are the same question — whether these bytes carry a declaration of
 * ours — and because the answer to it is a raise. Everything that turns that raise into a value is
 * in {@link ClassFileDeclarations}, which reads no class file at all: the whole of what this class
 * does is inside the one call that class guards, and a file that imports nothing of the class-file
 * API has nowhere to put a read that escaped it.
 *
 * <p>That is the arrangement and not an accident of where the lines fell. Parsing a class file does
 * not read it — the model is lazy, and a constant an annotation names is checked when the annotation
 * is asked for it — so a guard around part of the reading answers part of the malformed artifacts.
 * Measured on a real module's declarations class: of 470 single-byte corruptions, 202 refuse the
 * parse and 97 more parse and then refuse an accessor.
 *
 * <p>Nothing here decides what a reader is told. It raises, and says nothing about what that means.
 */
final class SoutherAnnotations {

    private SoutherAnnotations() {}

    /** The descriptors {@link ModuleMetadata} writes. Matched whole rather than by their last
     *  segment: a {@code SoutherData} of somebody else's package is not one of these, and reading it
     *  as one would take a stranger's annotation for a declaration of ours. */
    private static final String MODULE = "Lsouther/runtime/meta/SoutherModule;";
    private static final String DATA = "Lsouther/runtime/meta/SoutherData;";
    private static final String BEHAVIOR = "Lsouther/runtime/meta/SoutherBehavior;";

    /**
     * What one class was annotated with.
     *
     * @throws IllegalArgumentException where the bytes are not a class file this runtime reads, or
     *         carry metadata of this compiler's name that is not this compiler's shape. The two are
     *         one question here: what was asked for is a declaration of ours, and an annotation of
     *         our name carrying something else is no more one than a class file that will not parse.
     *         Read as a default instead, a {@code @SoutherData} with no {@code value} came back as a
     *         declaration whose text is empty, and the reading went on to answer with a module.
     */
    static PublishedClasses.Declarations in(byte[] bytes) {
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
     * <p>Absent and wrong are different answers and are told apart by every reader below. A member a
     * writer left out is the annotation's default, which is how a reader newer than the writer goes
     * on reading what it does carry; a member written as something the schema does not declare has
     * no default to fall back to, and the annotation is not one of ours.
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

    /** Raised for metadata of this compiler's name that is not this compiler's shape. */
    private static IllegalArgumentException notOurs(String member) {
        return new IllegalArgumentException(
                "`" + member + "` is not what this compiler writes there");
    }
}
