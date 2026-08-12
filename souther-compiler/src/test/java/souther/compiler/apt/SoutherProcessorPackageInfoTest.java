package souther.compiler.apt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;
import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.attribute.RuntimeVisibleAnnotationsAttribute;
import java.lang.constant.ClassDesc;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Java written in the same package as the module may declare a {@code package-info.java} of its own —
 * and in a project whose only Java is that file, it does. Nothing generated is named after it, so the
 * declaration stands and the module's types are marked all the same (issue #150).
 */
class SoutherProcessorPackageInfoTest {

    private static final ClassDesc NULL_MARKED = ClassDesc.of("org.jspecify.annotations.NullMarked");

    @Test
    void aHandWrittenPackageInfoCollidesWithNothing(@TempDir Path dir) throws IOException {
        Files.writeString(dir.resolve("module.sou"), """
                module app.order
                data Order = { id: String }
                """);
        Path pkg = Files.createDirectories(dir.resolve("app/order"));
        Files.writeString(pkg.resolve("package-info.java"), "package app.order;\n");

        List<String> warnings = compile(dir, pkg.resolve("package-info.java"));

        assertTrue(warnings.stream().noneMatch(w -> w.contains("souther:")),
                "the processor has nothing to report: " + warnings);
        Path order = dir.resolve("classes/app/order/Order.class");
        assertTrue(Files.exists(order), "the module is emitted as usual");
        assertEquals(List.of(NULL_MARKED), annotations(Files.readAllBytes(order)),
                "and its types are marked without the package saying anything");
    }

    /** Runs javac with the processor over {@code source}; the build must succeed. Returns its
     *  warnings. */
    private static List<String> compile(Path dir, Path source) throws IOException {
        Path classes = Files.createDirectories(dir.resolve("classes"));
        JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
        DiagnosticCollector<JavaFileObject> collected = new DiagnosticCollector<>();
        boolean ok;
        try (StandardJavaFileManager files =
                     javac.getStandardFileManager(collected, null, StandardCharsets.UTF_8)) {
            ok = javac.getTask(null, files, collected, List.of(
                    "-processor", SoutherProcessor.class.getName(),
                    "-Asouther.source=" + dir.resolve("module.sou"),
                    "-Asouther.lang=en",
                    "-d", classes.toString(),
                    "-classpath", System.getProperty("java.class.path")),
                    null, files.getJavaFileObjects(source)).call();
        }
        List<String> warnings = new ArrayList<>();
        List<String> errors = new ArrayList<>();
        for (Diagnostic<? extends JavaFileObject> d : collected.getDiagnostics()) {
            (d.getKind() == Diagnostic.Kind.ERROR ? errors : warnings)
                    .add(d.getMessage(Locale.ENGLISH));
        }
        assertTrue(ok && errors.isEmpty(), "the build carries on: " + errors);
        return warnings;
    }

    /** The annotation types the class carries as runtime-visible — what a Kotlin compiler reads. */
    private static List<ClassDesc> annotations(byte[] bytes) {
        return ClassFile.of().parse(bytes).findAttribute(java.lang.classfile.Attributes
                        .runtimeVisibleAnnotations())
                .map(RuntimeVisibleAnnotationsAttribute::annotations).orElse(List.of())
                .stream().map(a -> a.classSymbol()).toList();
    }
}
