package souther.compiler.apt;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.Messages;
import souther.compiler.diag.SourceContext;
import souther.compiler.Compiler;

import javax.annotation.processing.AbstractProcessor;
import javax.annotation.processing.Filer;
import javax.annotation.processing.RoundEnvironment;
import javax.annotation.processing.SupportedAnnotationTypes;
import javax.lang.model.SourceVersion;
import javax.lang.model.element.TypeElement;
import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

/**
 * A javac annotation processor that compiles Souther {@code .sou} sources to {@code .class} as a
 * side effect of an ordinary {@code javac} run (spec 4, 20). Point it at a directory (or a single
 * {@code .sou} file) with {@code -Asouther.source=<path>}; each module found is compiled and its
 * classes are emitted through the {@link Filer}, so hand-written Java in the same compilation can
 * reference the generated types directly.
 *
 * <p>This needs no build-tool plugin: it is discovered the standard way (Maven
 * {@code annotationProcessorPaths}, Gradle {@code annotationProcessor}, or plain
 * {@code javac -processorpath}). With no {@code souther.source} option it is a no-op, so it is
 * harmless to have on any classpath.
 *
 * <p>A compile error is rendered as the CLI renders it and handed to the {@code Messager}, so the
 * build log carries the snippet and the hint rather than an exception's detail string.
 * {@code -Asouther.lang=<tag>} chooses the language, defaulting the same way {@code souther --lang}
 * does.
 */
@SupportedAnnotationTypes("*")
public final class SoutherProcessor extends AbstractProcessor {

    private boolean done = false;

    @Override
    public SourceVersion getSupportedSourceVersion() {
        return SourceVersion.latestSupported();
    }

    @Override
    public Set<String> getSupportedOptions() {
        return Set.of("souther.source", "souther.lang");
    }

    @Override
    public boolean process(Set<? extends TypeElement> annotations, RoundEnvironment roundEnv) {
        if (done) {
            return false;
        }
        String configured = processingEnv.getOptions().get("souther.source");
        if (configured == null || configured.isBlank()) {
            return false;   // not configured: no-op
        }
        done = true;
        List<Source> sources = List.of();
        try {
            sources = readSources(Path.of(configured));
            if (sources.isEmpty()) {
                return false;
            }
            List<String> texts = sources.stream().map(Source::text).toList();
            Map<String, byte[]> classes = texts.size() == 1
                    ? Compiler.compile(texts.get(0))
                    : Compiler.compileModules(texts);
            Filer filer = processingEnv.getFiler();
            for (Map.Entry<String, byte[]> entry : classes.entrySet()) {
                JavaFileObject file = filer.createClassFile(entry.getKey());
                try (OutputStream out = file.openOutputStream()) {
                    out.write(entry.getValue());
                }
            }
        } catch (CompileException e) {
            for (String reported : render(e, sources)) {
                processingEnv.getMessager().printMessage(Diagnostic.Kind.ERROR, reported);
            }
        } catch (IOException e) {
            processingEnv.getMessager().printMessage(Diagnostic.Kind.ERROR, "souther: io error: " + e.getMessage());
        }
        return false;
    }

    /**
     * The compile error as the CLI would print it: an Elm-style snippet in the chosen locale, with
     * no color since this goes to a build log. The snippet comes from the source the compiler names
     * — the only one, or the module it was working on when a module set is linked. An error that
     * carries several diagnostics — every failing {@code example} row — is reported once per row.
     */
    private List<String> render(CompileException e, List<Source> sources) {
        if (e.diagnostic() == null) {
            return List.of("souther: " + e.getMessage());   // not yet structured
        }
        Source origin = originOf(e, sources);
        SourceContext src = origin == null ? null
                : new SourceContext(origin.path().getFileName().toString(), origin.text());
        Locale locale = Messages.resolveLocale(processingEnv.getOptions().get("souther.lang"));
        HumanRenderer renderer = new HumanRenderer(false);
        List<String> reported = new ArrayList<>();
        for (souther.compiler.diag.Diagnostic d : e.diagnostics()) {
            reported.add(renderer.render(d, src, locale));
        }
        return reported;
    }

    /** The source the error came from, or null when it names none (so no line is quoted). */
    private static Source originOf(CompileException e, List<Source> sources) {
        if (sources.size() == 1) {
            return sources.get(0);
        }
        int index = e.sourceIndex();
        return index >= 0 && index < sources.size() ? sources.get(index) : null;
    }

    /** Reads a single {@code .sou} file, or every {@code .sou} under a directory (path-sorted). */
    private static List<Source> readSources(Path path) throws IOException {
        if (Files.isDirectory(path)) {
            try (Stream<Path> walk = Files.walk(path)) {
                List<Path> files = walk.filter(p -> p.toString().endsWith(".sou")).sorted().toList();
                List<Source> sources = new ArrayList<>();
                for (Path file : files) {
                    sources.add(new Source(file, Files.readString(file)));
                }
                return sources;
            }
        }
        return List.of(new Source(path, Files.readString(path)));
    }

    /** A {@code .sou} file and its text. The path is kept so a diagnostic can quote the line. */
    private record Source(Path path, String text) {}
}
