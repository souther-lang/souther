package souther.compiler.apt;

import souther.compiler.CompilationSources;
import souther.compiler.CompilationSources.SourceFile;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.Located;
import souther.compiler.diag.Messages;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.Compiler;
import souther.compiler.query.Compilation;
import souther.compiler.meta.ModulePath;

import javax.annotation.processing.AbstractProcessor;
import javax.annotation.processing.Filer;
import javax.annotation.processing.RoundEnvironment;
import javax.annotation.processing.SupportedAnnotationTypes;
import javax.lang.model.SourceVersion;
import javax.lang.model.element.TypeElement;
import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;
import javax.tools.StandardLocation;
import java.io.IOException;
import java.io.InputStream;
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
 * A javac annotation processor that compiles Souther {@code .sou} sources to {@code .class} as a side effect
 * of an ordinary {@code javac} run (spec §modules, §compiler-pipeline). Point it at a directory (or a single
 * {@code .sou} file) with {@code -Asouther.source=<path>}; each module found is compiled and its classes are
 * emitted through the {@link Filer}, so hand-written Java in the same compilation can reference the generated
 * types directly.
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
        CompilationSources sources = CompilationSources.files(List.of());
        try {
            sources = readSources(Path.of(configured));
            if (sources.texts().isEmpty()) {
                return false;
            }
            // A module these sources import but do not contain is looked for on the compile
            // classpath — which is what depending on another project's jar already puts there, so
            // there is nothing to configure.
            ModulePath path = compileClassPath();
            List<Located> warnings = new ArrayList<>();
            Compilation compilation = Compiler.compiled(sources, path, warnings);
            // A warning is the whole of what the checker has to say about an unproven construction,
            // so a build that never reports one lets them accumulate while staying green.
            for (String reported : render(warnings, sources)) {
                processingEnv.getMessager().printMessage(Diagnostic.Kind.WARNING, reported);
            }
            Map<String, ClassFileImage> classes = compilation.classes();
            Filer filer = processingEnv.getFiler();
            for (Map.Entry<String, ClassFileImage> entry : classes.entrySet()) {
                JavaFileObject file = filer.createClassFile(entry.getKey());
                try (OutputStream out = file.openOutputStream()) {
                    out.write(entry.getValue().bytes());
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
     * no color since this goes to a build log. The snippet comes from the source the diagnostic
     * names. An error that carries several diagnostics — every failing {@code example} row — is
     * reported once per row.
     */
    private List<String> render(CompileException e, CompilationSources sources) {
        if (e.diagnostic() == null) {
            return List.of("souther: " + e.getMessage());   // not yet structured
        }
        return render(e.locatedDiagnostics(), sources);
    }

    /** The same rendering for a warning, which arrives already carrying the source it belongs to. */
    private List<String> render(List<Located> located, CompilationSources sources) {
        return DiagnosticRenderer.renderAll(
                located, sources.contexts(), new HumanRenderer(false), locale());
    }

    /**
     * The language this compile answers in: the {@code souther.lang} processor option if the build
     * passes one, then {@code SOUTHER_LANG}, then the default.
     *
     * <p>The processor's policy, in the processor. javac tells a processor nothing about who reads
     * its output, so the option is what there is to read; a build that passes none is answered like
     * a CLI invocation that named none.
     */
    private Locale locale() {
        return Messages.resolveLocale(processingEnv.getOptions().get("souther.lang"));
    }


    /**
     * The classes of the projects this compilation depends on, read through the {@link Filer}: javac
     * has already resolved the compile classpath, so nothing here has to be told where the jars are.
     * A class the classpath does not have reads as absent, which is how an import of a module that is
     * genuinely not there stays an unknown-module error where it is written.
     */
    private ModulePath compileClassPath() {
        Filer filer = processingEnv.getFiler();
        return binaryName -> {
            int lastDot = binaryName.lastIndexOf('.');
            String pkg = lastDot < 0 ? "" : binaryName.substring(0, lastDot);
            String simple = binaryName.substring(lastDot + 1) + ".class";
            try (InputStream in = filer.getResource(StandardLocation.CLASS_PATH, pkg, simple)
                    .openInputStream()) {
                return in.readAllBytes();
            } catch (IOException | IllegalArgumentException | UnsupportedOperationException _) {
                return null;
            }
        };
    }

    /** Reads a single {@code .sou} file, or every {@code .sou} under a directory (path-sorted). */
    private static CompilationSources readSources(Path path) throws IOException {
        if (Files.isDirectory(path)) {
            try (Stream<Path> walk = Files.walk(path)) {
                List<Path> files = walk.filter(p -> p.toString().endsWith(".sou")).sorted().toList();
                List<SourceFile> sources = new ArrayList<>();
                for (Path file : files) {
                    sources.add(new SourceFile(file.toString(), Files.readString(file)));
                }
                return CompilationSources.files(sources);
            }
        }
        return CompilationSources.files(
                List.of(new SourceFile(path.toString(), Files.readString(path))));
    }
}
