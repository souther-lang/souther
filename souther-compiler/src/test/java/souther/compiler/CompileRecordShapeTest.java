package souther.compiler;

import souther.compiler.diag.msg.DataMessage;
import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;
import java.io.IOException;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.TypeAnnotation;
import java.lang.classfile.attribute.RuntimeVisibleTypeAnnotationsAttribute;
import java.lang.reflect.RecordComponent;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Spec §jvm-product: a data / unit class is a record — {@code java.lang.Record} with a {@code Record}
 * attribute naming its fields as components. That is how a value reads at the boundary without the
 * reader being told anything: javac deconstructs it in a record pattern as it does the runtime's
 * {@code Ok} / {@code Err}, and Kotlin types each component as a property instead of resolving the
 * backing field and reporting that it cannot be accessed.
 */
class CompileRecordShapeTest {

    private static final String SRC = """
            module demo
            exposing ( Id, Member, Status, Active, Suspended )

            data Id = String
            data Member = { id: Id, age: Int, tags: List<String> }

            data Active
            data Suspended = { reason: String }
            data Status = Active | Suspended
            """;

    @Test
    void aDataIsARecordOverItsFields() throws Exception {
        Class<?> member = load().loadClass("demo.Member");

        assertTrue(member.isRecord(), "demo.Member is a record");
        assertEquals(List.of("id", "age", "tags"),
                java.util.Arrays.stream(member.getRecordComponents())
                        .map(RecordComponent::getName).toList(),
                "its components are the fields, in declaration order");
        assertEquals(List.of("demo.Id", "long", "java.util.List"),
                java.util.Arrays.stream(member.getRecordComponents())
                        .map(c -> c.getType().getTypeName()).toList());
    }

    @Test
    void aUnitCaseIsARecordWithNoComponents() throws Exception {
        Class<?> active = load().loadClass("demo.Active");

        assertTrue(active.isRecord(), "demo.Active is a record");
        assertEquals(0, active.getRecordComponents().length);
    }

    @Test
    void toStringPrintsTheRecordForm() throws Exception {
        BytesClassLoader loader = load();
        Object member = Codecs.decoded(loader.loadClass("demo.Member"),
                Map.of("id", "m-1", "age", 30L, "tags", List.of("staff")));

        assertEquals("Member[id=Id[value=m-1], age=30, tags=[staff]]", member.toString());
    }

    @Test
    void aUnitPrintsItsNameAndNoComponents() throws Exception {
        Class<?> active = load().loadClass("demo.Active");

        assertEquals("Active[]", active.getField("INSTANCE").get(null).toString());
    }

    /**
     * Kotlin types a record component from the component, which is the one place it does not apply the
     * class's {@code @NullMarked} — so the accessor says {@code @NonNull} on the return type itself,
     * at every position of it: the {@code List} and the {@code String} it holds.
     */
    @Test
    void anAccessorSaysEveryPositionOfItsTypeIsNonNull() {
        ClassModel member = ClassFile.of().parse(Compiler.compile(SRC).get("demo.Member"));

        assertEquals(List.of("[]"), nonNullPaths(member, "id"));
        assertEquals(List.of("[]", "[TYPE_ARGUMENT(0)]"), nonNullPaths(member, "tags"));
        assertEquals(List.of(), nonNullPaths(member, "age"),
                "an Int accessor returns a long, and a primitive has no nullness to state");
    }

    /**
     * The {@code Record} component repeats it, at the same positions: a reflective reader goes through
     * {@code RecordComponent#getAnnotatedType}, which reads the component rather than the accessor.
     */
    @Test
    void theRecordComponentRepeatsIt() {
        ClassModel member = ClassFile.of().parse(Compiler.compile(SRC).get("demo.Member"));

        assertEquals(List.of("[]"), componentNonNullPaths(member, "id"));
        assertEquals(List.of("[]", "[TYPE_ARGUMENT(0)]"), componentNonNullPaths(member, "tags"));
        assertEquals(List.of(), componentNonNullPaths(member, "age"),
                "a long component has no nullness to state either");
    }

    /**
     * A field is read through an accessor of its own name, so a no-argument method of {@code Object} is
     * a name no field can take: a field called {@code toString} would emit a second {@code toString()}
     * and the class would not load at all. {@code equals} is not one of them — {@code equals()} and
     * {@code equals(Object)} are different methods, and javac accepts it as a component name too.
     * Refused where the field is written.
     */
    @Test
    void aFieldNamedAfterAnObjectMethodIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Odd = { toString: String }
                """));

        assertInstanceOf(DataMessage.AFieldTakesAMethodOfObject.class, e.diagnostic().said(), e.getMessage());
    }

    @Test
    void aFieldNamedEqualsIsFine() throws Exception {
        Class<?> odd = new BytesClassLoader(Compiler.compile("""
                module demo
                exposing ( Odd )
                data Odd = { equals: String }
                """), getClass().getClassLoader()).loadClass("demo.Odd");

        assertTrue(odd.isRecord(), "the class loads and is a record");
        assertEquals(String.class, odd.getMethod("equals").getReturnType(),
                "`equals()` is the accessor and `equals(Object)` is value equality");
        assertEquals(boolean.class, odd.getMethod("equals", Object.class).getReturnType());
    }

    @Test
    void javacDeconstructsAGeneratedValueInARecordPattern(@TempDir Path dir) throws IOException {
        Path classes = write(dir, Compiler.compile(SRC));
        Path source = dir.resolve("Read.java");
        // the nested pattern reaches through the newtype, and the switch over the union is exhaustive
        // without a default: what a Java consumer gets from the shape, with nothing declared for it
        Files.writeString(source, """
                package app;

                import demo.Member;
                import demo.Status;
                import demo.Active;
                import demo.Suspended;

                public class Read {
                    static String of(Member m) {
                        if (m instanceof Member(demo.Id(String id), long age, var tags)) {
                            return id + age + tags;
                        }
                        return "";
                    }

                    static String of(Status s) {
                        return switch (s) {
                            case Active() -> "active";
                            case Suspended(String reason) -> reason;
                        };
                    }
                }
                """);

        assertEquals(List.of(), javac(source, classes, dir.resolve("out")));
    }

    private static BytesClassLoader load() {
        return new BytesClassLoader(Compiler.compile(SRC), CompileRecordShapeTest.class.getClassLoader());
    }

    /** The {@code @NonNull} type paths on the named accessor's return type, in the order emitted. */
    private static List<String> nonNullPaths(ClassModel model, String accessor) {
        MethodModel method = model.methods().stream()
                .filter(m -> m.methodName().stringValue().equals(accessor))
                .findFirst().orElseThrow();
        return nonNullPaths(method, TypeAnnotation.TargetType.METHOD_RETURN);
    }

    /** The same, on the named {@code Record} component. */
    private static List<String> componentNonNullPaths(ClassModel model, String component) {
        return nonNullPaths(model.findAttribute(Attributes.record()).orElseThrow()
                        .components().stream()
                        .filter(c -> c.name().stringValue().equals(component))
                        .findFirst().orElseThrow(),
                TypeAnnotation.TargetType.FIELD);
    }

    /** Reads {@code element}'s runtime-visible {@code @NonNull}s at {@code target} as type paths. The
     *  annotation is read off the class file rather than through reflection: JSpecify is `provided`, so
     *  a reflective read would drop what it cannot load and pass while saying nothing. */
    private static List<String> nonNullPaths(java.lang.classfile.AttributedElement element,
                                             TypeAnnotation.TargetType target) {
        return element.findAttribute(Attributes.runtimeVisibleTypeAnnotations())
                .map(RuntimeVisibleTypeAnnotationsAttribute::annotations).orElse(List.of())
                .stream()
                .filter(a -> a.annotation().classSymbol().displayName().equals("NonNull"))
                .filter(a -> a.targetInfo().targetType() == target)
                .map(a -> a.targetPath().stream()
                        .map(p -> p.typePathKind() + "(" + p.typeArgumentIndex() + ")")
                        .toList().toString())
                .toList();
    }

    /** Writes a compiled module out as class files a javac run can read. */
    private static Path write(Path dir, Map<String, byte[]> compiled) throws IOException {
        Path classes = Files.createDirectories(dir.resolve("classes"));
        for (Map.Entry<String, byte[]> e : compiled.entrySet()) {
            Path target = classes.resolve(e.getKey().replace('.', '/') + ".class");
            Files.createDirectories(target.getParent());
            Files.write(target, e.getValue());
        }
        return classes;
    }

    /** Compiles {@code source} against the generated classes, returning javac's diagnostics. */
    private static List<String> javac(Path source, Path classes, Path out) throws IOException {
        JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
        DiagnosticCollector<JavaFileObject> collected = new DiagnosticCollector<>();
        boolean ok;
        try (StandardJavaFileManager files =
                     javac.getStandardFileManager(collected, null, StandardCharsets.UTF_8)) {
            ok = javac.getTask(null, files, collected,
                    List.of("-d", Files.createDirectories(out).toString(),
                            "-classpath", classes.toString()),
                    null, files.getJavaFileObjects(source)).call();
        }
        List<String> reported = new ArrayList<>();
        collected.getDiagnostics().forEach(d -> reported.add(d.getMessage(Locale.ENGLISH)));
        assertTrue(ok, "javac accepts the patterns: " + reported);
        return reported;
    }
}
