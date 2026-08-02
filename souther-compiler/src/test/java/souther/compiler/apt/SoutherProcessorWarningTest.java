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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A warning the invariant checker finds reaches the build log the way an error does. The build is
 * what a project is actually verified by, so a warning it does not carry lets unproven constructions
 * accumulate while everything stays green.
 *
 * <p>javac's {@code Messager} positions a message by {@code Element}, and the construction is inside
 * a {@code .sou} file javac has no element for, so the rendered snippet is what carries the position
 * across — as it already does for an error.
 */
class SoutherProcessorWarningTest {

    /** One unproven construction, on line 9. */
    private static final String UNPROVEN = """
            module demo

            data Eaches = Int
                invariant value >= 0

            behavior wrap : (n: Int) -> Eaches
                constructs Eaches
            let wrap (n) = {
                let m = n
                Eaches(m)
            }
            """;

    @Test
    void anUnprovenConstructionIsReportedAsAWarningWithItsPosition(@TempDir Path dir)
            throws IOException {
        Path source = write(dir, "probe.sou", UNPROVEN);

        Reported reported = compile(dir, source, "en");

        assertTrue(reported.ok(), "a warning does not fail the build: " + reported.errors());
        assertTrue(reported.warnings().contains("probe.sou:10:5"), reported.warnings());
        assertTrue(reported.warnings().contains("Eaches(m)"), reported.warnings());
        assertTrue(reported.warnings().contains("^"), reported.warnings());
        assertTrue(reported.warnings().contains("E2011"), reported.warnings());
        assertTrue(reported.warnings().contains("INVARIANT (WARNING)"), reported.warnings());
    }

    @Test
    void theWarningFollowsTheChosenLanguage(@TempDir Path dir) throws IOException {
        Path source = write(dir, "probe.sou", UNPROVEN);

        Reported reported = compile(dir, source, "ja");

        assertTrue(reported.warnings().contains("(警告)"), reported.warnings());
        assertTrue(reported.warnings().contains("不変条件に違反する可能性があります"),
                reported.warnings());
    }

    @Test
    void aWarningInAModuleSetNamesTheFileItIsIn(@TempDir Path dir) throws IOException {
        Path sources = Files.createDirectories(dir.resolve("souther"));
        write(sources, "a.sou", """
                module a exposing ( Eaches, wrap )

                data Eaches = Int
                    invariant value >= 0

                behavior wrap : (n: Int) -> Eaches
                    constructs Eaches
                let wrap (n) = {
                    let m = n
                    Eaches(m)
                }
                """);
        write(sources, "b.sou", """
                module b

                import a ( Eaches )

                data Box = { it: Eaches }
                """);

        Reported reported = compile(dir, sources, "en");

        assertTrue(reported.ok(), reported.errors());
        assertTrue(reported.warnings().contains("a.sou:10:5"), reported.warnings());
        assertFalse(reported.warnings().contains("b.sou"), reported.warnings());
    }

    @Test
    void aCleanSourceReportsNothing(@TempDir Path dir) throws IOException {
        Path source = write(dir, "clean.sou", """
                module demo

                data Eaches = Int
                    invariant value >= 0

                behavior wrap : (n: Eaches) -> Eaches
                    constructs Eaches
                let wrap (n) = Eaches(n.value)
                """);

        Reported reported = compile(dir, source, "en");

        assertTrue(reported.ok(), reported.errors());
        assertTrue(reported.warnings().isBlank(), reported.warnings());
    }

    /** What javac reported, split by kind, and whether the compilation succeeded. */
    private record Reported(boolean ok, String errors, String warnings) {}

    /** Runs javac over one throwaway Java file with the processor pointed at {@code source}. */
    private static Reported compile(Path dir, Path source, String lang) throws IOException {
        Path java = write(dir, "Dummy.java", "public class Dummy {}\n");
        Path classes = Files.createDirectories(dir.resolve("classes"));
        JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
        DiagnosticCollector<JavaFileObject> collected = new DiagnosticCollector<>();
        boolean ok;
        try (StandardJavaFileManager files =
                     javac.getStandardFileManager(collected, null, StandardCharsets.UTF_8)) {
            List<String> options = new ArrayList<>(List.of(
                    "-processor", SoutherProcessor.class.getName(),
                    "-Asouther.source=" + source,
                    "-Asouther.lang=" + lang,
                    "-d", classes.toString(),
                    "-classpath", System.getProperty("java.class.path")));
            ok = javac.getTask(null, files, collected, options,
                    null, files.getJavaFileObjects(java)).call();
        }
        StringBuilder errors = new StringBuilder();
        StringBuilder warnings = new StringBuilder();
        for (Diagnostic<? extends JavaFileObject> d : collected.getDiagnostics()) {
            StringBuilder into = switch (d.getKind()) {
                case ERROR -> errors;
                case WARNING, MANDATORY_WARNING -> warnings;
                default -> null;
            };
            if (into != null) {
                into.append(d.getMessage(Locale.ENGLISH)).append('\n');
            }
        }
        return new Reported(ok, errors.toString(), warnings.toString());
    }

    private static Path write(Path dir, String name, String content) throws IOException {
        Path file = dir.resolve(name);
        Files.writeString(file, content);
        return file;
    }
}
