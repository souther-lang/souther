package souther.build.driver;

import souther.build.BuildDiagnostic;
import souther.build.BuildDiagnostic.Severity;
import souther.build.BuildRequest;
import souther.build.BuildResult;
import souther.build.SoutherBuildDriver;
import souther.compiler.CompilationSources;
import souther.compiler.CompilationSources.SourceFile;
import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.Located;
import souther.compiler.diag.Messages;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

/** Drives the compiler for a build plugin. */
public final class CompilerBuildDriver implements SoutherBuildDriver {

    @Override
    public BuildResult compile(BuildRequest request) {
        try {
            CompilationSources sources = read(request.sourcePaths());
            Locale locale = Messages.resolveLocale(request.languageTag());
            ModulePath path = ModulePath.ofClassPath(request.classPath());
            List<Located> warnings = new ArrayList<>();
            Compilation compilation;
            try {
                compilation = Compiler.compiled(sources, path, warnings, Adequacy.Asked.NOTHING);
            } catch (CompileException e) {
                return new BuildResult(false,
                        rendered(e.locatedDiagnostics(), sources, locale, Severity.ERROR));
            }
            write(compilation.classes(), request.outputDirectory(), request.stateDirectory());
            // A warning is the whole of what the checker has to say about an unproven construction,
            // so a build that never reports one lets them accumulate while staying green.
            return new BuildResult(true, rendered(warnings, sources, locale, Severity.WARNING));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /**
     * The diagnostics as the CLI would print them: an Elm-style snippet in the chosen locale, with
     * no color since this goes to a build log. One diagnostic renders to one message, so an error
     * carrying several — every failing {@code example} row — comes back as several.
     */
    private static List<BuildDiagnostic> rendered(List<Located> located, CompilationSources sources,
                                                  Locale locale, Severity severity) {
        List<BuildDiagnostic> out = new ArrayList<>();
        for (String message : DiagnosticRenderer.renderAll(
                located, sources.contexts(), new HumanRenderer(false), locale)) {
            out.add(new BuildDiagnostic(severity, message));
        }
        return out;
    }

    /**
     * The {@code .sou} the request names: a directory is read through, a file is read. Path-sorted
     * within each of them, and in the order they were given, so a source set with several
     * directories compiles the same way twice.
     */
    private static CompilationSources read(List<Path> sourcePaths) throws IOException {
        List<SourceFile> sources = new ArrayList<>();
        for (Path sourcePath : sourcePaths) {
            if (Files.isDirectory(sourcePath)) {
                try (Stream<Path> walk = Files.walk(sourcePath)) {
                    for (Path file : walk.filter(p -> p.toString().endsWith(".sou")).sorted().toList()) {
                        sources.add(new SourceFile(file.toString(), Files.readString(file)));
                    }
                }
            } else {
                sources.add(new SourceFile(sourcePath.toString(), Files.readString(sourcePath)));
            }
        }
        return CompilationSources.files(sources);
    }

    /** What this compile generated, from the last one, so it can be taken back. */
    private static final String GENERATED = "generated";

    /**
     * Each generated class under {@code outputDirectory}, at the path its binary name says, and away
     * with whatever the compile before this one put there and this one does not.
     *
     * <p>Taken back one file at a time, from a record of what was written, rather than by emptying
     * the directory: on Maven that directory is where javac writes too. A renamed module would
     * otherwise leave the old name's classes behind — its {@code $Module} among them, which is what
     * another project imports it by, so a build downstream would go on importing a module that is
     * no longer written anywhere.
     */
    private static void write(Map<String, ClassFileImage> classes, Path outputDirectory,
                              Path stateDirectory) throws IOException {
        Set<String> written = new LinkedHashSet<>();
        for (Map.Entry<String, ClassFileImage> entry : classes.entrySet()) {
            String relative = entry.getKey().replace('.', '/') + ".class";
            Path file = outputDirectory.resolve(relative);
            Files.createDirectories(file.getParent());
            Files.write(file, entry.getValue().bytes());
            written.add(relative);
        }
        remove(generatedBefore(stateDirectory), written, outputDirectory);
        Files.createDirectories(stateDirectory);
        Files.write(stateDirectory.resolve(GENERATED), written);
    }

    /** What the compile before this one wrote, or nothing when there was none. */
    private static List<String> generatedBefore(Path stateDirectory) throws IOException {
        Path record = stateDirectory.resolve(GENERATED);
        return Files.exists(record) ? Files.readAllLines(record) : List.of();
    }

    private static void remove(List<String> before, Set<String> written, Path outputDirectory)
            throws IOException {
        for (String previous : before) {
            if (previous.isBlank() || written.contains(previous)) {
                continue;
            }
            Path stale = outputDirectory.resolve(previous);
            Files.deleteIfExists(stale);
            emptyParents(stale.getParent(), outputDirectory);
        }
    }

    /** Up from a removed class, while a directory is left with nothing in it. */
    private static void emptyParents(Path from, Path outputDirectory) throws IOException {
        Path directory = from;
        while (directory != null && !directory.equals(outputDirectory)
                && directory.startsWith(outputDirectory) && Files.isDirectory(directory)) {
            try (Stream<Path> held = Files.list(directory)) {
                if (held.findAny().isPresent()) {
                    return;
                }
            }
            Files.delete(directory);
            directory = directory.getParent();
        }
    }
}
