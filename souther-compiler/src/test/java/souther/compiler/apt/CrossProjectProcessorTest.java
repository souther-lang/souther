package souther.compiler.apt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two builds, as two projects would run them: one compiles a module and keeps its classes, the other
 * depends on those classes and imports the module. The second has no {@code .sou} of the first and
 * is told nothing beyond its ordinary compile classpath — which is what depending on a jar already
 * puts there.
 */
class CrossProjectProcessorTest {

    @Test
    void anAppImportsAModuleAnotherProjectCompiled(@TempDir Path dir) throws IOException {
        Path libClasses = build(dir, "lib", """
                module shared.money exposing ( Amount )
                data Amount = Int
                    invariant value >= 0
                """, List.of());

        Path appClasses = build(dir, "app", """
                module app.order exposing ( Order, place )
                import shared.money ( Amount )
                data Order = { total: Amount }
                behavior place : (a: Amount) -> Order constructs Order
                let place (a) = Order { total = a }
                """, List.of(libClasses));

        assertTrue(Files.exists(appClasses.resolve("app/order/Order.class")));
        assertFalse(Files.exists(appClasses.resolve("shared/money/Amount.class")),
                "the dependency's classes belong to its own build");
    }

    /** With nothing on the classpath the import is what is wrong, and says so where it is written. */
    @Test
    void withoutTheDependencyTheImportIsUnknown(@TempDir Path dir) {
        IOException failure = null;
        try {
            build(dir, "app", """
                    module app.order
                    import shared.money ( Amount )
                    data Order = { total: Amount }
                    """, List.of());
        } catch (IOException e) {
            failure = e;
        }
        assertTrue(failure != null && failure.getMessage().contains("shared.money"),
                String.valueOf(failure));
    }

    /** Runs one project's build: javac over a throwaway Java file with the processor pointed at the
     * {@code .sou}, {@code classPath} on the compile classpath. Returns where the classes landed. */
    private static Path build(Path dir, String project, String source, List<Path> classPath)
            throws IOException {
        Path root = Files.createDirectories(dir.resolve(project));
        Files.writeString(root.resolve("module.sou"), source);
        Files.writeString(root.resolve("Dummy.java"), "public class Dummy {}\n");
        Path classes = Files.createDirectories(root.resolve("classes"));

        StringBuilder cp = new StringBuilder(System.getProperty("java.class.path"));
        for (Path entry : classPath) {
            cp.append(File.pathSeparator).append(entry);
        }
        JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
        DiagnosticCollector<JavaFileObject> collected = new DiagnosticCollector<>();
        boolean ok;
        try (StandardJavaFileManager files =
                     javac.getStandardFileManager(collected, null, StandardCharsets.UTF_8)) {
            ok = javac.getTask(null, files, collected, List.of(
                    "-processor", SoutherProcessor.class.getName(),
                    "-Asouther.source=" + root.resolve("module.sou"),
                    "-Asouther.lang=en",
                    "-d", classes.toString(),
                    "-classpath", cp.toString()),
                    null, files.getJavaFileObjects(root.resolve("Dummy.java"))).call();
        }
        if (!ok) {
            List<String> reported = new ArrayList<>();
            for (Diagnostic<? extends JavaFileObject> d : collected.getDiagnostics()) {
                if (d.getKind() == Diagnostic.Kind.ERROR) {
                    reported.add(d.getMessage(Locale.ENGLISH));
                }
            }
            throw new IOException(project + " did not build: " + String.join("\n", reported));
        }
        return classes;
    }
}
