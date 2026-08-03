package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Report;
import souther.compiler.query.Output;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The compiler pipeline facade: source → parse → derive → type check → ClassFile bytecode
 * (spec section 20). {@link #compile} handles a single self-contained module;
 * {@link #compileModules} links several modules through explicit imports (spec section 4).
 */
public final class Compiler {

    private Compiler() {}

    /** Compiles a single self-contained module (no imports) into binary class name → bytecode.
     * A source that omits the {@code module} header is named {@code Main} (the string API has no
     * file name to derive from; {@link Runner} passes the file-name stem instead). */
    public static Map<String, byte[]> compile(String source) {
        return compile(source, "Main");
    }

    /**
     * A compiled module with any non-fatal diagnostics (invariant-discharge warnings, etc.), each
     * carrying the source it belongs to so a caller can quote the line it is about.
     *
     * @param classes the generated classes, by binary name
     * @param locatedWarnings the warnings, each with the source that holds it
     */
    public record Compiled(Map<String, byte[]> classes, List<Located> locatedWarnings) {

        /** The warnings on their own, for a caller that only reads what they say. */
        public List<Diagnostic> warnings() {
            return locatedWarnings.stream().map(Located::diagnostic).toList();
        }
    }

    /** Compiles and returns the classes together with any invariant-discharge warnings. */
    public static Compiled compileWithWarnings(String source) {
        return compileWithWarnings(source, "Main");
    }

    /** As {@link #compileWithWarnings(String)}, but a header-less source is named
     * {@code defaultModuleName} (so the CLI's filename-stem naming can surface warnings too). */
    public static Compiled compileWithWarnings(String source, String defaultModuleName) {
        List<Located> warnings = new ArrayList<>();
        Map<String, byte[]> classes = compile(source, defaultModuleName, warnings);
        return new Compiled(classes, warnings);
    }

    /** As {@link #compile(String)}, but a header-less source is named {@code defaultModuleName}. */
    public static Map<String, byte[]> compile(String source, String defaultModuleName) {
        return compile(source, defaultModuleName, new ArrayList<>());
    }

    private static Map<String, byte[]> compile(String source, String defaultModuleName,
                                               List<Located> warningsOut) {
        try {
            return compiling(source, defaultModuleName, warningsOut);
        } catch (StackOverflowError _) {
            throw tooDeep();
        }
    }

    /**
     * A source whose expressions nest deeper than the compiler can walk. Every phase descends an
     * expression by recursion — parsing, inlining, checking, emitting — so past some depth the stack
     * runs out. That is not a {@code CompileException}, so left alone it passes through the recovery
     * boundary and reaches the author as a stack trace, and takes the language server's dispatch
     * loop with it. It is reported like any other thing the compiler cannot accept.
     *
     * <p>The depth is not a written limit, so no position is claimed: the failure belongs to the
     * source as a whole, and the author's move is the same wherever it landed — name the parts.
     */
    private static CompileException tooDeep() {
        return CompileException.of(
                Diagnostic.of(null, "check.expr.toodeep").title("check.boundary.title").build(),
                "an expression in this source nests too deeply for the compiler to walk;"
                        + " name its parts with `let` to flatten it");
    }

    /**
     * Compiles one self-contained source by asking one compilation for its classes.
     *
     * <p>This differs from {@link #linking} in what it lets a source be, not in what it does with
     * it: a source with no {@code module} header takes a name, and a failing example is reported
     * with its own position rather than tagged with the file it came from, because there is only
     * the one.
     */
    private static Map<String, byte[]> compiling(String source, String defaultModuleName,
                                                 List<Located> warningsOut) {
        return classesOf(compiled(source, defaultModuleName, warningsOut));
    }

    /**
     * The compilation of one self-contained source, driven to completion, with the first error
     * raised. A caller that wants more than the classes — what a module declares, what a behavior's
     * signature is — asks the compilation rather than parsing the source a second time.
     */
    public static Compilation compiled(String source, String defaultModuleName) {
        return compiled(source, defaultModuleName, new ArrayList<>());
    }

    /** As {@link #compiled(String, String)}, collecting the compile's warnings into
     *  {@code warningsOut}. */
    static Compilation compiled(String source, String defaultModuleName,
                                List<Located> warningsOut) {
        return compiled(source, defaultModuleName, warningsOut, Adequacy.Asked.NOTHING);
    }

    /** As above, telling the compile how much of the rows' coverage to measure and warn about. */
    static Compilation compiled(String source, String defaultModuleName,
                                List<Located> warningsOut, Adequacy.Asked measure) {
        Compilation compilation = Compilation.ofSource(source, defaultModuleName);
        compilation.measure(measure);
        Db db = compilation.db();

        CompileException structural = compilation.firstError(compilation.structuralReports());
        if (structural != null) {
            throw structural;
        }

        db.ask(new Output.All());
        CompileException failed = compilation.firstError(db.allReports());
        if (failed != null) {
            throw failed;
        }
        for (String module : compilation.modules()) {
            if (!db.ask(new Output.ConstConstructions(module)).present()) {
                CompileException bad = compilation.firstError(db.allReports());
                if (bad != null) {
                    throw bad;
                }
            }
            List<Diagnostic> failures = new ArrayList<>();
            for (String id : compilation.exampleSourcesOf(module)) {
                // Only the errors: this key also carries what a clean run wants to say about how well
                // the rows cover the model, and a warning is not a reason to fail the build.
                for (Report failure : Report.errorsIn(db.ask(new Output.Examples(module, id)).reports())) {
                    failures.add(failure.diagnostic());
                }
            }
            if (failures.size() == 1) {
                throw CompileException.of(failures.get(0),
                        ExampleVerifier.legacySummary(failures));
            }
            if (!failures.isEmpty()) {
                throw CompileException.ofAll(failures, ExampleVerifier.legacySummary(failures));
            }
        }
        for (String module : compilation.modules()) {
            db.ask(new Adequacy.Warnings(module));
        }
        warningsOut.addAll(compilation.warnings(db.allReports()));
        return compilation;
    }

    private static Map<String, byte[]> classesOf(Compilation compilation) {
        return new LinkedHashMap<>(compilation.classes());
    }

    /** Compiles a set of modules together, resolving explicit imports and rejecting cycles. */
    public static Map<String, byte[]> compileModules(List<String> sources) {
        return compileModules(sources, ModulePath.EMPTY);
    }

    /**
     * As {@link #compileModules(List)}, but an import naming no module among {@code sources} is
     * resolved against {@code path} — the compiled modules of the projects this one depends on. A
     * module found there is read for its declarations and nothing else: its classes are already
     * built, and this compile neither re-emits them nor re-runs its examples.
     */
    public static Map<String, byte[]> compileModules(List<String> sources, ModulePath path) {
        return compileModules(sources, path, new ArrayList<>());
    }

    /** Links a module set like {@link #compileModules(List)} and returns the classes with any
     * invariant-discharge warnings from every module. */
    public static Compiled compileModulesWithWarnings(List<String> sources) {
        return compileModulesWithWarnings(sources, ModulePath.EMPTY);
    }

    /** As {@link #compileModulesWithWarnings(List)}, resolving against {@code path} as
     * {@link #compileModules(List, ModulePath)} does. */
    public static Compiled compileModulesWithWarnings(List<String> sources, ModulePath path) {
        List<Located> warnings = new ArrayList<>();
        return new Compiled(compileModules(sources, path, warnings), warnings);
    }

    private static Map<String, byte[]> compileModules(List<String> sources, ModulePath path,
                                                      List<Located> warningsOut) {
        try {
            return linking(sources, path, warningsOut);
        } catch (StackOverflowError _) {
            throw tooDeep();
        }
    }

    /**
     * Links a set of sources by asking one compilation for its classes.
     *
     * <p>What is left here is only what a batch compile decides and an editor decides differently:
     * that a structural problem stops everything, that the first error is raised rather than
     * collected, and that every module's examples are evaluated before any failing one is reported
     * (issue #114) — so a change to a widely-imported data says how far it reaches in one compile.
     */
    /**
     * The compilation of a module set, driven to completion, with the first error raised — what
     * {@link #linking} returns the classes of, for a caller that wants more than the classes.
     *
     * <p>{@code souther examples} is such a caller: it asks how well the rows cover the model, which
     * is read off the same compile that would have written the classes out.
     */
    public static Compilation compiledModules(List<String> sources, ModulePath path,
                                              List<Located> warningsOut) {
        return linked(sources, path, warningsOut, Adequacy.Asked.NOTHING);
    }

    /** As above, telling the compile how much of the rows' coverage to measure and warn about. */
    public static Compilation compiledModules(List<String> sources, ModulePath path,
                                              List<Located> warningsOut, Adequacy.Asked measure) {
        return linked(sources, path, warningsOut, measure);
    }

    private static Map<String, byte[]> linking(List<String> sources, ModulePath path,
                                               List<Located> warningsOut) {
        return new LinkedHashMap<>(
                linked(sources, path, warningsOut, Adequacy.Asked.NOTHING).classes());
    }

    private static Compilation linked(List<String> sources, ModulePath path,
                                      List<Located> warningsOut, Adequacy.Asked measure) {
        Compilation compilation = Compilation.ofSources(sources, path);
        compilation.measure(measure);
        Db db = compilation.db();

        CompileException structural = compilation.firstError(compilation.structuralReports());
        if (structural != null) {
            throw structural;
        }

        db.ask(new Output.All());
        CompileException failed = compilation.firstError(db.allReports());
        if (failed != null) {
            throw failed;
        }

        // Every module's classes are now present, so a constant construction and an example can
        // resolve a cross-module reference — including into a dependency, whose classes come off the
        // same path its declarations were read from.
        List<Diagnostic> exampleFailures = new ArrayList<>();
        List<Integer> exampleSources = new ArrayList<>();
        for (String module : compilation.modules()) {
            if (!db.ask(new Output.ConstConstructions(module)).present()) {
                CompileException bad = compilation.firstError(db.allReports());
                if (bad != null) {
                    throw bad;
                }
                continue;
            }
            for (String id : compilation.exampleSourcesOf(module)) {
                for (Report failure : Report.errorsIn(db.ask(new Output.Examples(module, id)).reports())) {
                    exampleFailures.add(failure.diagnostic());
                    // a row from an `examples for` file is positioned in that file, not this one
                    exampleSources.add(compilation.sourceIndexOfId(id));
                }
            }
        }
        for (String module : compilation.modules()) {
            db.ask(new Adequacy.Warnings(module));
        }
        warningsOut.addAll(compilation.warnings(db.allReports()));
        if (!exampleFailures.isEmpty()) {
            throw CompileException.ofAllInSources(exampleFailures, exampleSources,
                    ExampleVerifier.legacySummary(exampleFailures));
        }
        return compilation;
    }
    /**
     * Links a module set like {@link #compileModules}, but collects diagnostics per source — keyed by
     * the caller's id (the LSP passes a document URI) — instead of throwing on the first error. This is
     * the entry point the LSP uses to publish diagnostics per file across a workspace.
     *
     * <p>Modules are compiled in dependency order (imports first); a module's first compile error is
     * recorded under its source id and its downstream importers are skipped, so an error surfaces once
     * at its origin rather than cascading. Examples are then evaluated per source: a module's inline
     * examples land on that module's id, and an {@code examples for X} file's examples land on that
     * file's id — never on the target module. A source with no problem maps to an empty list.
     */
    public static Map<String, List<Diagnostic>> diagnoseModules(Map<String, String> sourcesById) {
        return diagnoseModules(sourcesById, Set.of());
    }

    /**
     * As {@link #diagnoseModules(Map)}, but {@code brokenModuleNames} lists modules the caller has
     * already found unparseable (a file the LSP holds out of the compile because of its own syntax
     * errors). Their importers are skipped rather than told the module is unknown — the error belongs
     * to the broken file, which reports it separately, not to the importer.
     */
    public static Map<String, List<Diagnostic>> diagnoseModules(Map<String, String> sourcesById,
                                                                Set<String> brokenModuleNames) {
        return diagnoseModules(sourcesById, brokenModuleNames, ModulePath.EMPTY);
    }

    /**
     * As {@link #diagnoseModules(Map, Set)}, resolving an import that names no module among
     * {@code sourcesById} against {@code path}, the way a build does. Without this an editor reports
     * an unknown module for an import the build resolves, which is the wrong answer twice over.
     *
     * <p>A path that is itself wrong — a module missing behind a module — is not reported here. The
     * editor's job is the source in front of the author, and a broken path is the build's to say.
     */
    public static Map<String, List<Diagnostic>> diagnoseModules(Map<String, String> sourcesById,
                                                                Set<String> brokenModuleNames,
                                                                ModulePath path) {
        return Compilation.ofDocuments(sourcesById, brokenModuleNames, path).diagnostics();
    }
    /** The module name from a source's {@code module <name>} header, for identifying a source that will
     * not parse (so its importers can be skipped, and the LSP can map a broken file to its module).
     * {@code null} if no header token is found. */
    public static String moduleNameFromHeader(String source) {
        java.util.regex.Matcher mt = java.util.regex.Pattern
                .compile("(?m)^\\s*module\\s+([\\p{L}\\p{N}_.]+)").matcher(source);
        return mt.find() ? mt.group(1) : null;
    }
    /** Compiles source and writes each generated class under {@code outDir}. */
    public static void compileToDir(String source, Path outDir) throws IOException {
        for (Map.Entry<String, byte[]> entry : compile(source).entrySet()) {
            Path file = outDir.resolve(entry.getKey().replace('.', '/') + ".class");
            Files.createDirectories(file.getParent());
            Files.write(file, entry.getValue());
        }
    }
}
