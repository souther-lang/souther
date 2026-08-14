package souther.compiler;

import souther.compiler.jvm.JvmClassName;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.diag.Located;
import souther.compiler.examples.Deadline;
import souther.compiler.examples.EvaluationPolicy;
import souther.compiler.examples.ExampleVerifier;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Front;
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
 * (spec §compiler-pipeline). {@link #compile} handles a single self-contained module;
 * {@link #compileModules} links several modules through explicit imports (spec §modules).
 */
public final class Compiler {

    private Compiler() {}

    /** Compiles a single self-contained module (no imports) into binary class name → bytecode.
     * A source that omits the {@code module} header is named {@code Main} (the string API has no
     * file name to derive from; {@code souther run} passes the file-name stem instead). */
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
        return compiling(source, defaultModuleName, warningsOut);
    }

    /**
     * Drives one compilation with the recovery every entry point here answers by.
     *
     * <p>Around the three places a compilation is driven, rather than around the entry points that
     * reach them. It was written on the entry points that answer with classes, and the ones that
     * answer with a {@link Compilation} — which is what the command line and the editor ask for —
     * had nothing, so the same source was a diagnostic through one door and a stack trace through
     * another. What decides the answer is the compiler, not which signature a caller reached for.
     *
     * <p>Around what an entry point does with the compilation as well as around the driving of it.
     * Taking the classes off a driven compilation reads a key the driver already asked, so it walks
     * nothing today — but that is a fact about the order two lines happen to be in, and a region
     * that holds only while they stay in it is not a boundary. Nesting is why it can be said twice:
     * the inner one answers first, and the outer one covers what is left.
     */
    static <T> T driven(java.util.function.Supplier<T> compilation) {
        try {
            return compilation.get();
        } catch (StackOverflowError _) {
            throw tooDeep();
        }
    }

    /**
     * The compiler ran out of room. Every phase descends what it builds by recursion, so a walk
     * that is handed something deep enough exhausts the stack — which is not a
     * {@code CompileException}, so left alone it passes through the recovery boundary and reaches
     * the author as a stack trace. It is reported like any other thing the compiler cannot accept.
     *
     * <p>Not a report about nesting. What a source may nest is bounded as it is read, and what a
     * definition may say is bounded over what it says, so on the stack this compiler is supported
     * on a source that got past both should not arrive here. Arriving here says the stack was
     * smaller than that, or that something builds depth no bound is holding — neither of which the
     * author can be told to flatten.
     *
     * <p>No position is claimed: where the stack ended is not a fact about the source.
     */
    private static CompileException tooDeep() {
        return CompileException.of(Diagnostic.say(new DeclarationMessage.TheCompilerRanOutOfRoom()).build());
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
        return driven(() -> classesOf(compiled(source, defaultModuleName, warningsOut)));
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

    /** As above, telling the compile how much of the rows' coverage to measure and warn about.
     *  Public for the same reason {@link #compiledModules(List, ModulePath, List, Adequacy.Asked)}
     *  is: a caller outside this package compiles one source and measures it. */
    public static Compilation compiled(String source, String defaultModuleName,
                                       List<Located> warningsOut, Adequacy.Asked measure) {
        return compiled(source, defaultModuleName, warningsOut, measure, null, null);
    }

    /**
     * As above, on a budget of its own for each row evaluated and each statement read.
     *
     * <p>{@code null} takes the default, which is what every caller outside this compiler's own tests
     * wants: it is set so that no terminating row is cut short, and a build has no other requirement
     * of it. What a shorter one is for is a model written so that a row does not come back — see
     * {@link Compilation#withExampleBudget}.
     */
    static Compilation compiled(String source, String defaultModuleName,
                                List<Located> warningsOut, Adequacy.Asked measure,
                                java.time.Duration exampleBudget) {
        return compiled(source, defaultModuleName, warningsOut, measure, exampleBudget, null);
    }

    /** As above, on a policy of its own — the steps and the depth a row is decided by. */
    static Compilation compiled(String source, String defaultModuleName,
                                List<Located> warningsOut, Adequacy.Asked measure,
                                EvaluationPolicy policy) {
        return compiled(source, defaultModuleName, warningsOut, measure, null, null, policy);
    }

    /** As above, with what a row or a reading is given to finish within said outright — for a test
     *  stating which work does not come back rather than timing it. */
    static Compilation compiled(String source, String defaultModuleName,
                                List<Located> warningsOut, Adequacy.Asked measure,
                                java.time.Duration exampleBudget, Deadline deadline) {
        return compiled(source, defaultModuleName, warningsOut, measure, exampleBudget, deadline, null);
    }

    /**
     * The compilation of one source, resolving an import that names no module in it against
     * {@code path} — what {@code run} asks for, holding one file and a class path.
     */
    public static Compilation compiled(String source, String defaultModuleName,
                                       List<Located> warningsOut, ModulePath path) {
        return driven(() -> compilingSource(source, defaultModuleName, warningsOut,
                Adequacy.Asked.NOTHING, null, null, null, path));
    }

    private static Compilation compiled(String source, String defaultModuleName,
                                        List<Located> warningsOut, Adequacy.Asked measure,
                                        java.time.Duration exampleBudget, Deadline deadline,
                                        EvaluationPolicy policy) {
        return driven(() -> compilingSource(source, defaultModuleName, warningsOut, measure,
                exampleBudget, deadline, policy, ModulePath.EMPTY));
    }

    private static Compilation compilingSource(String source, String defaultModuleName,
                                               List<Located> warningsOut, Adequacy.Asked measure,
                                               java.time.Duration exampleBudget, Deadline deadline,
                                               EvaluationPolicy policy, ModulePath path) {
        Compilation compilation = Compilation.ofSource(source, defaultModuleName, path);
        if (exampleBudget != null) {
            compilation.withExampleBudget(exampleBudget);
        }
        if (deadline != null) {
            compilation.withDeadline(deadline);
        }
        if (policy != null) {
            compilation.withEvaluationPolicy(policy);
        }
        compilation.measure(measure);
        Db db = compilation.db();

        CompileException structural = compilation.failure(compilation.structuralReports());
        if (structural != null) {
            throw structural;
        }

        db.ask(new Output.All());
        CompileException failed = compilation.failure(db.allReports());
        if (failed != null) {
            throw failed;
        }
        for (String module : compilation.modules()) {
            if (!db.ask(new Output.ConstConstructions(module)).present()) {
                CompileException bad = compilation.failure(db.allReports());
                if (bad != null) {
                    throw bad;
                }
            }
            List<Diagnostic> failures = new ArrayList<>();
            for (String id : compilation.exampleSourcesOf(module)) {
                // What the rows name themselves, before what they state: a name says which row is
                // meant, and two rows sharing one leave every later report about either of them
                // saying it of both.
                for (Report failure : Report.errorsIn(db.ask(new Front.RowNames(id)).reports())) {
                    failures.add(failure.diagnostic());
                }
                // Only the errors: this key also carries what a clean run wants to say about how well
                // the rows cover the model, and a warning is not a reason to fail the build.
                for (Report failure : Report.errorsIn(db.ask(Output.Examples.asked(db, module, id)).reports())) {
                    failures.add(failure.diagnostic());
                }
            }
            // Asked whether or not the rows ran: what two written statements say about each other
            // is readable when nothing is.
            db.ask(new Output.SaidDisagreements(module));
            if (failures.size() == 1) {
                throw CompileException.of(failures.get(0));
            }
            if (!failures.isEmpty()) {
                throw CompileException.ofAll(failures, ExampleVerifier.legacySummary(failures));
            }
        }
        for (String module : compilation.modules()) {
            compilation.answerWarnings(module);
        }
        warningsOut.addAll(compilation.warnings(db.allReports()));
        return compilation;
    }

    /**
     * The compilation of one source, driven as far as it goes, with nothing raised.
     *
     * <p>Beside {@link #compiled} rather than in place of it. A caller about to write classes out has
     * to stop at the first error, there being nothing to write; a caller about to say what the rows
     * cover has an answer either way. The specification puts the two apart — an example report
     * "changes what compiles" not at all — and this is the half of that the entry points did not
     * have. What refused the compilation is refused still: it is in the reports, and the caller reads
     * it there rather than catching it.
     */
    public static Compilation analyzed(String source, String defaultModuleName,
                                       List<Located> warningsOut, Adequacy.Asked measure) {
        return answered(Compilation.ofSource(source, defaultModuleName), warningsOut, measure);
    }

    /** As {@link #analyzed}, for a module set resolved against {@code path} — what
     *  {@link #compiledModules} is to {@link #compiled}. */
    public static Compilation analyzedModules(List<String> sources, ModulePath path,
                                              List<Located> warningsOut, Adequacy.Asked measure) {
        return answered(Compilation.ofSources(sources, path), warningsOut, measure);
    }

    /**
     * Asks the whole compilation and collects its warnings.
     *
     * <p>The warnings are collected whatever the compilation came to, which is where this parts from
     * the raising entry points: they reach the collection only by getting past every error, so a
     * compilation with one reports no warnings at all. Nothing about a warning depends on the errors
     * beside it.
     *
     * <p>Running out of stack is the one thing this raises. An error is an answer — it is in the
     * reports, and the compilation around it stands — but a walk that ran out returned nothing to
     * put there, and the questions below it have no answers either. There is no partial reading to
     * hand back, so this says what it is instead of handing back a compilation that looks clean.
     */
    private static Compilation answered(Compilation compilation, List<Located> warningsOut,
                                        Adequacy.Asked measure) {
        return driven(() -> {
            compilation.measure(measure);
            compilation.answerEverything();
            warningsOut.addAll(compilation.warnings(compilation.db().allReports()));
            return compilation;
        });
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
        return linking(sources, path, warningsOut);
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
     * <p>For a caller that has to have a compilation there is nothing to go on with. A caller that
     * can say something either way takes {@link #analyzedModules} instead.
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
        return driven(() -> new LinkedHashMap<>(
                linked(sources, path, warningsOut, Adequacy.Asked.NOTHING).classes()));
    }

    /** As {@link #compiledModules(List, ModulePath, List, Adequacy.Asked)}, on a budget of its own
     *  for each row evaluated — {@code null} takes the default. See
     *  {@link #compiled(String, String, List, Adequacy.Asked, java.time.Duration)}. */
    static Compilation compiledModules(List<String> sources, ModulePath path,
                                       List<Located> warningsOut, Adequacy.Asked measure,
                                       java.time.Duration exampleBudget) {
        return linked(sources, path, warningsOut, measure, exampleBudget, null, null);
    }

    /** As above, on a policy of its own — the steps and the depth a row is decided by. */
    static Compilation compiledModules(List<String> sources, ModulePath path,
                                       List<Located> warningsOut, Adequacy.Asked measure,
                                       EvaluationPolicy policy) {
        return linked(sources, path, warningsOut, measure, null, null, policy);
    }

    /** As above, with what a row or a reading is given to finish within said outright. */
    static Compilation compiledModules(List<String> sources, ModulePath path,
                                       List<Located> warningsOut, Adequacy.Asked measure,
                                       java.time.Duration exampleBudget, Deadline deadline) {
        return linked(sources, path, warningsOut, measure, exampleBudget, deadline, null);
    }

    private static Compilation linked(List<String> sources, ModulePath path,
                                      List<Located> warningsOut, Adequacy.Asked measure) {
        return linked(sources, path, warningsOut, measure, null, null, null);
    }

    private static Compilation linked(List<String> sources, ModulePath path,
                                      List<Located> warningsOut, Adequacy.Asked measure,
                                      java.time.Duration exampleBudget, Deadline deadline,
                                      EvaluationPolicy policy) {
        return driven(() -> linkingSources(sources, path, warningsOut, measure, exampleBudget,
                deadline, policy));
    }

    private static Compilation linkingSources(List<String> sources, ModulePath path,
                                              List<Located> warningsOut, Adequacy.Asked measure,
                                              java.time.Duration exampleBudget, Deadline deadline,
                                              EvaluationPolicy policy) {
        Compilation compilation = Compilation.ofSources(sources, path);
        if (exampleBudget != null) {
            compilation.withExampleBudget(exampleBudget);
        }
        if (deadline != null) {
            compilation.withDeadline(deadline);
        }
        if (policy != null) {
            compilation.withEvaluationPolicy(policy);
        }
        compilation.measure(measure);
        Db db = compilation.db();

        CompileException structural = compilation.failure(compilation.structuralReports());
        if (structural != null) {
            throw structural;
        }

        db.ask(new Output.All());
        CompileException failed = compilation.failure(db.allReports());
        if (failed != null) {
            throw failed;
        }

        // Every module's classes are now present, so a constant construction and an example can
        // resolve a cross-module reference — including into a dependency, whose classes come off the
        // same path its declarations were read from.
        List<Diagnostic> exampleFailures = new ArrayList<>();
        List<String> exampleSources = new ArrayList<>();
        for (String module : compilation.modules()) {
            if (!db.ask(new Output.ConstConstructions(module)).present()) {
                CompileException bad = compilation.failure(db.allReports());
                if (bad != null) {
                    throw bad;
                }
                continue;
            }
            for (String id : compilation.exampleSourcesOf(module)) {
                for (Report failure : Report.errorsIn(db.ask(Output.Examples.asked(db, module, id)).reports())) {
                    exampleFailures.add(failure.diagnostic());
                    // a row from an `examples for` file is positioned in that file, not this one
                    exampleSources.add(id);
                }
            }
            db.ask(new Output.SaidDisagreements(module));
        }
        for (String module : compilation.modules()) {
            compilation.answerWarnings(module);
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
    public static Map<String, List<Located>> diagnoseModules(Map<String, String> sourcesById) {
        return diagnoseModules(sourcesById, Set.of());
    }

    /**
     * As {@link #diagnoseModules(Map)}, but {@code brokenModuleNames} lists modules the caller has
     * already found unparseable (a file the LSP holds out of the compile because of its own syntax
     * errors). Their importers are skipped rather than told the module is unknown — the error belongs
     * to the broken file, which reports it separately, not to the importer.
     */
    public static Map<String, List<Located>> diagnoseModules(Map<String, String> sourcesById,
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
    public static Map<String, List<Located>> diagnoseModules(Map<String, String> sourcesById,
                                                             Set<String> brokenModuleNames,
                                                             ModulePath path) {
        return Compilation.ofDocuments(sourcesById, brokenModuleNames, path).diagnostics();
    }
    /**
     * The module name from a source's {@code module <name>} header, for identifying a source that
     * will not parse (so its importers can be skipped, and the LSP can map a broken file to its
     * module). {@code null} if no header token is found.
     *
     * <p>Only for a source a compilation does not have. Which module a source is part of is
     * {@link souther.compiler.query.Front.ModuleOf}'s to answer, and this cannot answer it: an
     * {@code examples for} file writes no header and is part of a module all the same, so what
     * comes back here is nothing rather than the module its rows are for.
     */
    public static String moduleNameFromHeader(String source) {
        java.util.regex.Matcher mt = java.util.regex.Pattern
                .compile("(?m)^\\s*module\\s+([\\p{L}\\p{N}_.]+)").matcher(source);
        return mt.find() ? mt.group(1) : null;
    }
    /** Compiles source and writes each generated class under {@code outDir}. */
    public static void compileToDir(String source, Path outDir) throws IOException {
        for (Map.Entry<String, byte[]> entry : compile(source).entrySet()) {
            Path file = outDir.resolve(JvmClassName.classFile(entry.getKey()));
            Files.createDirectories(file.getParent());
            Files.write(file, entry.getValue());
        }
    }
}
