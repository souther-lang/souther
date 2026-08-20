package souther.cli.init;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.compiler.Compiler;
import souther.compiler.diag.Located;
import souther.compiler.jvm.JvmClassName;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;

import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The Java test a project starts with is compiled against the model that project starts with.
 *
 * <p>The one thing a `.sou` template cannot answer for itself. What the generated Java names — the
 * behavior's interface, the union its cases arrive in, a record's accessor — is the ABI, and a
 * template that fell behind it would produce a project whose first {@code mvn test} does not
 * compile. Reading it here means javac says so instead of a reader.
 */
class TheGeneratedTestCompilesAgainstTheGeneratedModelTest {

    private static final Project PROJECT = new Project(new Coordinate("com.example", "hello"),
            "com.example.hello", Model.FULL, BuildSystem.MAVEN, "9.9.9");

    @Test
    void theTestShippedWithTheFullModelCompilesAgainstIt(@TempDir Path directory) throws Exception {
        Path classes = Files.createDirectories(directory.resolve("classes"));
        write(compiled(), classes);

        DiagnosticCollector<JavaFileObject> problems = compile(source(), classes, directory);

        assertTrue(problems.getDiagnostics().stream()
                        .noneMatch(d -> d.getKind() == javax.tools.Diagnostic.Kind.ERROR),
                "the generated test does not compile against the generated model:\n"
                        + problems.getDiagnostics());
    }

    /** The classes the model compiles to, by binary name. */
    private static Map<String, byte[]> compiled() {
        List<String> texts = Templates.sourcesOf(PROJECT).stream()
                .filter(file -> file.path().endsWith(".sou"))
                .map(Templates.File::content)
                .toList();
        List<Located> warnings = new ArrayList<>();
        return Compiler.compiledModules(texts, ModulePath.EMPTY, warnings, Adequacy.Asked.NOTHING)
                .classes();
    }

    /** The Java the project starts with, as javac reads a source. */
    private static JavaFileObject source() {
        Templates.File test = Templates.sourcesOf(PROJECT).stream()
                .filter(file -> file.path().endsWith(".java"))
                .findFirst()
                .orElseThrow(() -> new AssertionError("the full model ships no Java test"));
        String name = test.path().substring(test.path().lastIndexOf('/') + 1);
        return new SimpleJavaFileObject(URI.create("string:///" + name), JavaFileObject.Kind.SOURCE) {
            @Override
            public CharSequence getCharContent(boolean ignoreEncodingErrors) {
                return test.content();
            }
        };
    }

    private static void write(Map<String, byte[]> classes, Path into) throws IOException {
        for (Map.Entry<String, byte[]> entry : classes.entrySet()) {
            Path file = into.resolve(JvmClassName.classFile(entry.getKey()));
            Files.createDirectories(file.getParent());
            Files.write(file, entry.getValue());
        }
    }

    /**
     * Compiles the source against the model's classes and this test run's own class path.
     *
     * <p>The class path is where the runtime and JUnit come from: what a generated project declares
     * as dependencies, this module already has.
     */
    private static DiagnosticCollector<JavaFileObject> compile(JavaFileObject source, Path classes,
                                                               Path into) throws IOException {
        JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
        DiagnosticCollector<JavaFileObject> problems = new DiagnosticCollector<>();
        try (StandardJavaFileManager files = javac.getStandardFileManager(problems, null, null)) {
            List<String> options = List.of(
                    "-classpath", classes + java.io.File.pathSeparator
                            + System.getProperty("java.class.path"),
                    "-d", Files.createDirectories(into.resolve("out")).toString());
            javac.getTask(null, files, problems, options, null, List.of(source)).call();
        }
        return problems;
    }
}
