package souther.compiler.meta;

import souther.compiler.Compiler;
import souther.compiler.jvm.ClassFileImage;

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
        Map<String, ClassFileImage> classes = new java.util.LinkedHashMap<>(Compiler.compile(SOURCE));
        ClassFile cf = ClassFile.of();
        ClassModel model = cf.parse(classes.get(binaryName).bytes());
        List<Annotation> had = new ArrayList<>();
        model.findAttribute(Attributes.runtimeInvisibleAnnotations())
                .ifPresent(a -> had.addAll(a.annotations()));
        classes.put(binaryName, ClassFileImage.of(cf.transformClass(model, ClassTransform
                .dropping(a -> a instanceof RuntimeInvisibleAnnotationsAttribute)
                .andThen(ClassTransform.endHandler(b -> b.with(
                        RuntimeInvisibleAnnotationsAttribute.of(as.apply(had))))))));
        return new ClassFileDeclarations(ModulePath.of(classes)::bytes);
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

    /**
     * Two of one annotation are two answers to a question the schema gives one.
     *
     * <p>A class file carries its annotations as a list, and nothing in the format makes one of a
     * type unique — none of these is declared repeatable, so the rule is this schema's and the
     * reading is what holds an artifact to it. Read in a loop that assigns as it goes, the second
     * quietly won: a class carrying two declarations published whichever came last, and nothing
     * anywhere said the other was there.
     */
    @Test
    void twoOfOneAnnotation() {
        PublishedClasses classes = withMetadata("shared.money.Amount", _ -> List.of(
                Annotation.of(DATA, AnnotationElement.ofString("value", "data Amount = Int")),
                Annotation.of(DATA, AnnotationElement.ofString("value", "data Amount = String"))));

        assertInstanceOf(PublishedClasses.Carried.UnreadableMetadata.class,
                classes.of("shared.money.Amount"),
                "neither of them is the declaration, and the later one is not more so");
    }

    /** The same, of the annotation a module's declarations are stamped on. */
    @Test
    void twoOfTheModuleAnnotation() {
        PublishedClasses classes = withMetadata("shared.money.$Module",
                had -> List.of(had.get(0), had.get(0)));

        assertInstanceOf(PublishedClasses.Carried.UnreadableMetadata.class,
                classes.of("shared.money.$Module"));
    }

    /** And one member written twice inside one annotation. */
    @Test
    void oneMemberWrittenTwice() {
        PublishedClasses classes = withMetadata("shared.money.Amount",
                _ -> List.of(Annotation.of(DATA,
                        AnnotationElement.ofString("value", "data Amount = Int"),
                        AnnotationElement.ofString("value", "data Amount = String"))));

        assertInstanceOf(PublishedClasses.Carried.UnreadableMetadata.class,
                classes.of("shared.money.Amount"),
                "which one is read was the order they happened to be written in");
    }

    /**
     * An annotation that is not ours may be there as often as it likes.
     *
     * <p>The control. What is refused is two answers to a question this schema asks, and a class
     * this compiler generated carrying somebody else's annotation twice asks it nothing.
     */
    @Test
    void twoOfSomebodyElsesAnnotation() {
        PublishedClasses classes = withMetadata("shared.money.Amount", had -> {
            List<Annotation> all = new ArrayList<>(had);
            all.add(Annotation.of(ClassDesc.of("elsewhere.Marker")));
            all.add(Annotation.of(ClassDesc.of("elsewhere.Marker")));
            return all;
        });

        PublishedClasses.Carried.Declared read = assertInstanceOf(
                PublishedClasses.Carried.Declared.class, classes.of("shared.money.Amount"));
        org.junit.jupiter.api.Assertions.assertNotNull(read.declarations().data());
    }

    /**
     * One place reads a class file, and it is not the one that decides what a lookup answers.
     *
     * <p>Whether a malformed artifact ends the compilation comes down to whether every read of it
     * happens inside the guard that turns a raise into an answer. Java cannot say that, and a test
     * that corrupts bytes and watches can only ever sample it — the reading that escaped the guard
     * before this was the lazy half, and a sample that dies on the eager half stays green over it.
     *
     * <p>So the guard is a file boundary. {@code SoutherAnnotations} is the whole of the reading and
     * is called once, from inside the guard; {@code ClassFileDeclarations} decides what is answered
     * and names nothing of the class-file API, so a read hoisted into it is an import this reads.
     *
     * <p>Written over the sources for the reason {@code EveryDiagnosticCodeIsReadableTest} says of
     * its own rule: the next one of these is a failing test rather than a malformed artifact quietly
     * ending a compile again.
     */
    @Test
    void oneFileInThisPackageReadsAClassFile() throws java.io.IOException {
        List<String> reading = new ArrayList<>();
        for (java.nio.file.Path source : souther.compiler.diag
                .EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources()) {
            String path = source.toString().replace('\\', '/')
                    .replaceAll(".*/src/main/java/", "");
            if (!path.startsWith("souther/compiler/meta/")) {
                continue;
            }
            if (java.nio.file.Files.readString(source, java.nio.charset.StandardCharsets.UTF_8)
                    .contains("java.lang.classfile")) {
                reading.add(path);
            }
        }
        java.util.Collections.sort(reading);

        org.junit.jupiter.api.Assertions.assertEquals(
                List.of("souther/compiler/meta/ModuleMetadata.java",
                        "souther/compiler/meta/SoutherAnnotations.java"),
                reading,
                "one writes the metadata and one reads it; anything else here that touches a class"
                        + " file is a read outside the guard that answers a malformed one, which is"
                        + " how a jar ended the compilation instead of being reported");
    }

    /** And the metadata this compiler does write is read. */
    @Test
    void whatThisCompilerWritesIsRead() {
        PublishedClasses classes = new ClassFileDeclarations(ModulePath.of(Compiler.compile(SOURCE))::bytes);

        PublishedClasses.Carried.Declared read = assertInstanceOf(
                PublishedClasses.Carried.Declared.class, classes.of("shared.money.Amount"));
        org.junit.jupiter.api.Assertions.assertNotNull(read.declarations().data());
    }
}
