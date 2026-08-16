package souther.compiler.meta;

import souther.compiler.Compiler;

import org.junit.jupiter.api.Test;

import java.lang.classfile.Annotation;
import java.lang.classfile.AnnotationElement;
import java.lang.classfile.AnnotationValue;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.ClassTransform;
import java.lang.classfile.attribute.RuntimeInvisibleAnnotationsAttribute;
import java.lang.constant.ClassDesc;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * An annotation of this compiler's name carrying something this compiler does not write is metadata
 * it cannot read, and not metadata with values left at their defaults.
 *
 * <p>Reading a class file and reading the metadata on it are two things, and the class-file model
 * answers only the first. It gives back the annotations and their members as they were written; that
 * {@code SoutherData} is declared with a {@code value} of type {@code String}, and with no default,
 * is this compiler's schema and nothing the model holds anyone to. So a member written as an int, or
 * not written at all, came back through a reader that coerced it — and a {@code @SoutherData} with
 * no {@code value} became a declaration whose text is empty, which the reading went on to accept.
 *
 * <p>Absent is not the same as wrong. A member a writer left out is the schema's default, which is
 * how a reader newer than the writer goes on reading what it does carry; a member written as
 * something the schema does not declare belongs to no version of it.
 */
class MetadataOfThisCompilersNameIsHeldToItsShapeTest {

    private static final ClassDesc DATA = ClassDesc.of("souther.runtime.meta.SoutherData");
    private static final ClassDesc MODULE = ClassDesc.of("souther.runtime.meta.SoutherModule");

    private static final String SOURCE = """
            module shared.money exposing ( Amount )
            data Amount = Int
            """;

    /** {@code binaryName}'s class with its annotations rewritten. */
    private static PublishedClasses withMetadata(String binaryName,
                                                 UnaryOperator<List<Annotation>> as) {
        Map<String, byte[]> classes = new java.util.LinkedHashMap<>(Compiler.compile(SOURCE));
        ClassFile cf = ClassFile.of();
        ClassModel model = cf.parse(classes.get(binaryName));
        List<Annotation> had = new ArrayList<>();
        model.findAttribute(Attributes.runtimeInvisibleAnnotations())
                .ifPresent(a -> had.addAll(a.annotations()));
        classes.put(binaryName, cf.transformClass(model, ClassTransform
                .dropping(a -> a instanceof RuntimeInvisibleAnnotationsAttribute)
                .andThen(ClassTransform.endHandler(b -> b.with(
                        RuntimeInvisibleAnnotationsAttribute.of(as.apply(had)))))));
        return new ClassFileDeclarations(classes::get);
    }

    /** A member the schema declares with no default, and the writer always writes. */
    @Test
    void aRequiredMemberThatIsNotThereAtAll() {
        PublishedClasses classes = withMetadata("shared.money.Amount",
                _ -> List.of(Annotation.of(DATA)));

        assertInstanceOf(PublishedClasses.Carried.UnreadableMetadata.class,
                classes.of("shared.money.Amount"),
                "a declaration with no text is not a declaration whose text is empty");
    }

    /** The same member, written as something else. */
    @Test
    void aRequiredMemberOfAnotherType() {
        PublishedClasses classes = withMetadata("shared.money.Amount",
                _ -> List.of(Annotation.of(DATA, AnnotationElement.ofInt("value", 7))));

        assertInstanceOf(PublishedClasses.Carried.UnreadableMetadata.class,
                classes.of("shared.money.Amount"));
    }

    /** A member the schema does declare a default for, written as something that is not it. */
    @Test
    void aDefaultedMemberOfAnotherType() {
        PublishedClasses classes = withMetadata("shared.money.$Module", had -> {
            List<AnnotationElement> members = new ArrayList<>();
            for (Annotation a : had) {
                if (a.className().stringValue().equals("Lsouther/runtime/meta/SoutherModule;")) {
                    for (AnnotationElement e : a.elements()) {
                        members.add(e.name().stringValue().equals("types")
                                ? AnnotationElement.ofString("types", "Amount") : e);
                    }
                }
            }
            return List.of(Annotation.of(MODULE, members));
        });

        assertInstanceOf(PublishedClasses.Carried.UnreadableMetadata.class,
                classes.of("shared.money.$Module"),
                "the default is for a member nobody wrote, not for one written as something else");
    }

    /** An array of the right kind carrying an element that is not. */
    @Test
    void aDefaultedMemberHoldingSomethingThatIsNotAString() {
        PublishedClasses classes = withMetadata("shared.money.$Module", had -> {
            List<AnnotationElement> members = new ArrayList<>();
            for (Annotation a : had) {
                if (a.className().stringValue().equals("Lsouther/runtime/meta/SoutherModule;")) {
                    for (AnnotationElement e : a.elements()) {
                        members.add(e.name().stringValue().equals("types")
                                ? AnnotationElement.of("types",
                                        AnnotationValue.ofArray(AnnotationValue.ofInt(1)))
                                : e);
                    }
                }
            }
            return List.of(Annotation.of(MODULE, members));
        });

        assertInstanceOf(PublishedClasses.Carried.UnreadableMetadata.class,
                classes.of("shared.money.$Module"));
    }

    /**
     * An annotation of somebody else's package with one of these names is not one of these.
     *
     * <p>Matched on the last segment of the descriptor, a {@code SoutherData} anyone declares is read
     * as a declaration of ours, and whatever it carries becomes the text of a type.
     */
    @Test
    void anAnnotationOfThatNameFromSomewhereElse() {
        PublishedClasses classes = withMetadata("shared.money.Amount",
                _ -> List.of(Annotation.of(ClassDesc.of("elsewhere.SoutherData"),
                        AnnotationElement.ofString("value", "data Amount = String"))));

        PublishedClasses.Carried.Declared read = assertInstanceOf(
                PublishedClasses.Carried.Declared.class, classes.of("shared.money.Amount"));
        org.junit.jupiter.api.Assertions.assertNull(read.declarations().data(),
                "a stranger's annotation is not a declaration this compiler published");
    }

    /** And the metadata this compiler does write is read. */
    @Test
    void whatThisCompilerWritesIsRead() {
        PublishedClasses classes = new ClassFileDeclarations(Compiler.compile(SOURCE)::get);

        PublishedClasses.Carried.Declared read = assertInstanceOf(
                PublishedClasses.Carried.Declared.class, classes.of("shared.money.Amount"));
        org.junit.jupiter.api.Assertions.assertNotNull(read.declarations().data());
    }
}
