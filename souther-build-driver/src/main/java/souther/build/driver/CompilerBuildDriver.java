package souther.build.driver;

import souther.build.BuildDiagnostic;
import souther.build.BuildDiagnostic.Severity;
import souther.build.BuildRequest;
import souther.build.BuildResult;
import souther.build.SoutherBuildDriver;
import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.Located;
import souther.compiler.diag.Messages;
import souther.compiler.diag.SourceContext;
import souther.compiler.diag.SourceContextResolver;
import souther.compiler.diag.SourceNames;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.stream.Stream;

/** Drives the compiler for a build plugin. */
public final class CompilerBuildDriver implements SoutherBuildDriver {

    @Override
    public BuildResult compile(BuildRequest request) {
        try {
            List<Source> sources = read(request.sourcePaths());
            List<String> texts = sources.stream().map(Source::text).toList();
            Locale locale = Messages.resolveLocale(request.languageTag());
            // One source with no `module` header is a self-contained module and can import nothing;
            // one that names itself is a module set of one, and may import a module off the path.
            boolean selfContained =
                    texts.size() == 1 && Compiler.moduleNameFromHeader(texts.get(0)) == null;
            Compiler.Compiled compiled;
            try {
                compiled = selfContained
                        ? Compiler.compileWithWarnings(texts.get(0))
                        : Compiler.compileModulesWithWarnings(
                                texts, ModulePath.ofClassPath(request.classPath()));
            } catch (CompileException e) {
                return new BuildResult(false,
                        rendered(e.locatedDiagnostics(), sources, locale, Severity.ERROR));
            }
            write(compiled.classes(), request.outputDirectory());
            // A warning is the whole of what the checker has to say about an unproven construction,
            // so a build that never reports one lets them accumulate while staying green.
            return new BuildResult(true,
                    rendered(compiled.locatedWarnings(), sources, locale, Severity.WARNING));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /**
     * The diagnostics as the CLI would print them: an Elm-style snippet in the chosen locale, with
     * no color since this goes to a build log. One diagnostic renders to one message, so an error
     * carrying several — every failing {@code example} row — comes back as several.
     */
    private static List<BuildDiagnostic> rendered(List<Located> located, List<Source> sources,
                                                  Locale locale, Severity severity) {
        List<BuildDiagnostic> out = new ArrayList<>();
        for (String message : DiagnosticRenderer.renderAll(
                located, sourcesOf(sources), new HumanRenderer(false), locale)) {
            out.add(new BuildDiagnostic(severity, message));
        }
        return out;
    }

    /** What to quote for each source a diagnostic points into, under names no two of these files
     *  share. The text is already in hand, so this memoizes only to keep one answer per id. */
    private static SourceContextResolver sourcesOf(List<Source> sources) {
        List<String> names = SourceNames.of(
                sources.stream().map(source -> source.path().toString()).toList());
        return SourceContextResolver.memoized(id -> {
            int at = indexOf(sources, id);
            return at < 0 ? null : new SourceContext(names.get(at), sources.get(at).text());
        });
    }

    /** Which of the sources handed over an id names, or -1 when it names none of them. A compile of
     *  one source names none, and the one file it was given is the answer however it is tagged. */
    private static int indexOf(List<Source> sources, String sourceId) {
        if (sources.size() == 1) {
            return 0;
        }
        for (int i = 0; i < sources.size(); i++) {
            if (Compilation.idOfSourceIndex(i).equals(sourceId)) {
                return i;
            }
        }
        return -1;
    }

    /**
     * The {@code .sou} the request names: a directory is read through, a file is read. Path-sorted
     * within each of them, and in the order they were given, so a source set with several
     * directories compiles the same way twice.
     */
    private static List<Source> read(List<Path> sourcePaths) throws IOException {
        List<Source> sources = new ArrayList<>();
        for (Path sourcePath : sourcePaths) {
            if (Files.isDirectory(sourcePath)) {
                try (Stream<Path> walk = Files.walk(sourcePath)) {
                    for (Path file : walk.filter(p -> p.toString().endsWith(".sou")).sorted().toList()) {
                        sources.add(new Source(file, Files.readString(file)));
                    }
                }
            } else {
                sources.add(new Source(sourcePath, Files.readString(sourcePath)));
            }
        }
        return sources;
    }

    /** Each generated class under {@code outputDirectory}, at the path its binary name says. */
    private static void write(Map<String, byte[]> classes, Path outputDirectory) throws IOException {
        for (Map.Entry<String, byte[]> entry : classes.entrySet()) {
            Path file = outputDirectory.resolve(entry.getKey().replace('.', '/') + ".class");
            Files.createDirectories(file.getParent());
            Files.write(file, entry.getValue());
        }
    }

    /** A {@code .sou} file and its text. The path is kept so a diagnostic can quote the line. */
    private record Source(Path path, String text) {}
}
