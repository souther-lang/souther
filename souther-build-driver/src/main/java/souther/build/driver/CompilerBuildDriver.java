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
import souther.compiler.io.ConfinedTree;
import souther.compiler.io.ConfinementException;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

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
                compilation = Compiler.compiled(sources, path, warnings);
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
                sources.addAll(CompilationSources.readTree(sourcePath));
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
        ConfinedTree output = ConfinedTree.at(outputDirectory);
        ConfinedTree state = ConfinedTree.at(stateDirectory);
        Set<String> written = new LinkedHashSet<>();
        for (Map.Entry<String, ClassFileImage> entry : classes.entrySet()) {
            String relative = entry.getKey().replace('.', '/') + ".class";
            output.write(relative, entry.getValue().bytes());
            written.add(relative);
        }
        remove(generatedBefore(state), written, output);
        state.write(GENERATED, String.join("\n", written).concat("\n").getBytes(StandardCharsets.UTF_8));
    }

    /** What the compile before this one wrote, or nothing when there was none. */
    private static List<String> generatedBefore(ConfinedTree state) throws IOException {
        return state.isRegularFile(GENERATED)
                ? state.readString(GENERATED, MOST_BYTES_OF_THE_RECORD).lines().toList() : List.of();
    }

    /**
     * Takes back what an earlier compile wrote and this one did not.
     *
     * <p>The record is a file on disk, so a line in it names a file only as far as the output tree
     * agrees: a line that goes outside the tree, or through a link in it, is skipped and deletes
     * nothing.
     */
    private static void remove(List<String> before, Set<String> written, ConfinedTree output)
            throws IOException {
        for (String previous : before) {
            if (previous.isBlank() || written.contains(previous)) {
                continue;
            }
            try {
                output.deleteIfExists(previous);
                output.deleteEmptyParents(previous);
            } catch (ConfinementException _) {
                continue;
            }
        }
    }

    private static final long MOST_BYTES_OF_THE_RECORD = 64L * 1024 * 1024;
}
