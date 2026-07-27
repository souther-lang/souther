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
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The generated package annotations (the {@code package-info} carrying {@code @NullMarked}) are the
 * one generated class a hand-written source can be holding the name of: Java written in the same
 * package as the module may declare a {@code package-info.java} of its own. That is a declaration in
 * this compilation, so it wins — but the module's types then say nothing about null, which is worth
 * a word rather than a silent difference or a failed build.
 */
class SoutherProcessorPackageInfoTest {

    @Test
    void aHandWrittenPackageInfoWinsAndIsWarnedAbout(@TempDir Path dir) throws IOException {
        Files.writeString(dir.resolve("module.sou"), """
                module app.order
                data Order = { id: String }
                """);
        Path pkg = Files.createDirectories(dir.resolve("app/order"));
        Files.writeString(pkg.resolve("package-info.java"), "package app.order;\n");

        List<String> warnings = compile(dir, pkg.resolve("package-info.java"));

        assertTrue(warnings.stream().anyMatch(w -> w.contains("app.order.package-info")
                        && w.contains("@NullMarked")),
                "the skipped marking is reported: " + warnings);
        assertTrue(Files.exists(dir.resolve("classes/app/order/Order.class")),
                "the rest of the module is emitted as usual");
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
}
