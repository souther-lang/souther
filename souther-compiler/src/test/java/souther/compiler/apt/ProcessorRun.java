package souther.compiler.apt;

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

/**
 * One javac run with {@link SoutherProcessor} pointed at a {@code .sou} file or directory, and what
 * it reported, split by kind. The processor's whole surface to a build is what reaches the
 * {@code Messager}, so a test asserts on that text rather than on anything the compiler returns.
 *
 * @param ok whether the compilation succeeded — false when the processor reported an error
 * @param errors every {@code ERROR} message, one per line
 * @param warnings every {@code WARNING} message, one per line
 */
record ProcessorRun(boolean ok, String errors, String warnings) {

    /**
     * Runs javac over one throwaway Java file with the processor reading {@code source}, rendering
     * its diagnostics in {@code lang}. {@code dir} holds the scratch Java file and output classes.
     */
    static ProcessorRun of(Path dir, Path source, String lang) throws IOException {
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
        return new ProcessorRun(ok, errors.toString(), warnings.toString());
    }

    static Path write(Path dir, String name, String content) throws IOException {
        Path file = dir.resolve(name);
        Files.writeString(file, content);
        return file;
    }
}
