package souther.compiler;

import souther.compiler.cst.CstError;
import souther.compiler.cst.CstParser;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.JsonRenderer;
import souther.compiler.diag.Located;
import souther.compiler.diag.Messages;
import souther.compiler.diag.SourceContext;
import souther.compiler.diag.SourceContextResolver;
import souther.compiler.fmt.Formatter;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;

/**
 * CLI entry point with two subcommands: {@code souther compile <file.sou>... -d <outdir>} writes
 * {@code .class} files, and {@code souther run <file.sou> [--behavior <name>] [--input <json>]}
 * drives one behavior and prints its output (see {@link Runner}).
 *
 * <p>Both accept {@code --format human|json}, {@code --lang <tag>}, and {@code --color auto|always|never}
 * to control how a compile error is rendered (an Elm-style snippet or a JSON object, in the chosen
 * locale). These are pulled off before the subcommand's own arguments are parsed.
 */
public final class Main {

    private static final String USAGE = """
            usage: souther <command> [args]
            commands:
              compile <file.sou>... -d <outdir> [-cp <path>]      compile to .class files
              run <file.sou> [--behavior <name>] [--input <json>]  run a behavior, print its output
              fmt <file.sou>... [-w] [--check]                     format source (stdout, or -w in place)
              examples <file.sou>... [-cp <path>]                  how well the `example`s cover the model
            options (examples):
              --module <name>           report only this module
              --behavior <name>         report only this behavior
              --generate                print commented rows for what nothing covers
              --boundaries              with --generate, add rows at the untried boundaries
              --strict                  exit non-zero while rows are waiting for a `let`
            options (compile):
              --adequacy off|witness|all  warn about what the `example`s do not cover (default off)
            options (compile/examples):
              -cp, --class-path <path>  where to find modules another project compiled

            options (compile/run/examples):
              --format human|json      how to render a compile error (default: human)
              --lang <tag>             message locale, e.g. ja or en (default: system, then ja)
              --color auto|always|never  color the human output (default: auto)""";

    public static void main(String[] args) {
        String command = args.length == 0 ? "" : args[0];
        String[] rest = args.length == 0 ? args : java.util.Arrays.copyOfRange(args, 1, args.length);
        switch (command) {
            case "run" -> runSubcommand(rest);
            case "compile" -> compileSubcommand(rest);
            case "fmt" -> fmtSubcommand(rest);
            case "examples" -> examplesSubcommand(rest);
            default -> {
                String hint = command.endsWith(".sou")
                        ? "no command given — did you mean `souther compile " + command
                                + " …` or `souther run " + command + " …`?"
                        : command.isEmpty() ? "no command given" : "unknown command `" + command + "`";
                System.err.println(hint);
                System.err.println(USAGE);
                System.exit(2);
            }
        }
    }

    /** {@code souther compile <file.sou>... -d <outdir>}: writes the generated {@code .class} files. */
    private static void compileSubcommand(String[] rawArgs) {
        RenderOptions render = new RenderOptions();
        String[] args = render.extract(rawArgs);
        List<Path> sources = new ArrayList<>();
        List<Path> classPath = new ArrayList<>();
        Path outDir = Path.of(".");
        Adequacy.Asked measure = Adequacy.Asked.NOTHING;
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--adequacy" -> {
                    if (++i >= args.length || adequacyLevel(args[i]) == null) {
                        System.err.println("`--adequacy` takes off, witness or all");
                        System.exit(2);
                        return;
                    }
                    measure = Adequacy.Asked.warningsAt(adequacyLevel(args[i]));
                }
                case "-d" -> {
                    if (++i >= args.length) {
                        System.err.println("`-d` needs an output directory");
                        System.err.println(USAGE);
                        System.exit(2);
                        return;
                    }
                    outDir = Path.of(args[i]);
                }
                case "-cp", "--class-path" -> {
                    if (++i >= args.length) {
                        System.err.println("`" + args[i - 1] + "` needs a class path");
                        System.err.println(USAGE);
                        System.exit(2);
                        return;
                    }
                    for (String entry : args[i].split(java.io.File.pathSeparator)) {
                        if (!entry.isBlank()) {
                            classPath.add(Path.of(entry));
                        }
                    }
                }
                default -> sources.add(Path.of(args[i]));
            }
        }
        if (sources.isEmpty()) {
            System.err.println("compile takes at least one .sou file");
            System.err.println(USAGE);
            System.exit(2);
            return;
        }
        List<Located> warnings = new ArrayList<>();
        try {
            List<Path> written = compileToDir(sources, outDir, classPath, warnings, measure);
            // Before the written files: the warnings are about the source, and a long list of paths
            // between them and the command would bury them.
            report(warnings, sources, render);
            for (Path file : written) {
                System.out.println("wrote " + file);
            }
        } catch (CompileException e) {
            reportCompileError(e, sources, render);
            System.exit(1);
        } catch (IOException e) {
            // The compile itself finished — these warnings are the whole set, and what stopped the
            // command was writing the classes out, which says nothing about the source.
            report(warnings, sources, render);
            System.err.println("io error: " + e.getMessage());
            System.exit(1);
        }
    }

    /**
     * {@code souther examples <file.sou>...}: how well the model's {@code example}s cover it.
     *
     * <p>Its own command rather than a flag on {@code compile}, because the two answer different
     * questions. {@code compile} writes classes out and stops at the first error; this asks a model
     * that already compiles how much of it the rows have pinned down. Mixing them would put a report
     * on stdout next to {@code wrote <path>} and make a failing build the only way to see it.
     */
    private static void examplesSubcommand(String[] rawArgs) {
        RenderOptions render = new RenderOptions();
        String[] args = render.extract(rawArgs);
        List<Path> sources = new ArrayList<>();
        List<Path> classPath = new ArrayList<>();
        String module = null;
        String behavior = null;
        boolean strict = false;
        boolean generate = false;
        boolean boundaries = false;
        // The report is this command's whole output, so everything is measured and nothing is said
        // twice: what the warnings would say, the report says in one place.
        Adequacy.Asked measure = Adequacy.Asked.reportOnly();
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "-cp", "--class-path" -> {
                    if (++i >= args.length) {
                        System.err.println("`" + args[i - 1] + "` needs a class path");
                        System.err.println(USAGE);
                        System.exit(2);
                        return;
                    }
                    for (String entry : args[i].split(java.io.File.pathSeparator)) {
                        if (!entry.isBlank()) {
                            classPath.add(Path.of(entry));
                        }
                    }
                }
                case "--module" -> {
                    if (++i >= args.length) {
                        System.err.println("`--module` needs a module name");
                        System.exit(2);
                        return;
                    }
                    module = args[i];
                }
                case "--behavior" -> {
                    if (++i >= args.length) {
                        System.err.println("`--behavior` needs a behavior name");
                        System.exit(2);
                        return;
                    }
                    behavior = args[i];
                }
                case "--generate" -> generate = true;
                case "--boundaries" -> boundaries = true;
                case "--strict" -> strict = true;
                default -> sources.add(Path.of(args[i]));
            }
        }
        if (sources.isEmpty()) {
            System.err.println("examples takes at least one .sou file");
            System.err.println(USAGE);
            System.exit(2);
            return;
        }
        List<Located> warnings = new ArrayList<>();
        try {
            List<String> texts = new ArrayList<>();
            for (Path source : sources) {
                texts.add(Files.readString(source));
            }
            ModulePath path = classPath.isEmpty() ? ModulePath.EMPTY
                    : ModulePath.ofClassPath(classPath);
            Compilation compilation = texts.size() == 1 && classPath.isEmpty()
                    ? Compiler.compiled(texts.get(0), Runner.moduleName(sources.get(0)), warnings,
                            measure)
                    : Compiler.compiledModules(texts, path, warnings, measure);
            AdequacyReport report = AdequacyReport.of(compilation).only(module, behavior);
            report(warnings, sources, render);
            String rendered = render.json() ? report.json() + System.lineSeparator() : report.human();
            System.out.print(rendered);
            // After the report, because the rows are what to do about what the report just said.
            // Beside it rather than in it where the report is JSON: the rows are source, and source in
            // the middle of a JSON document is not a document.
            if (generate) {
                String rows = GeneratedRows.of(compilation, module, behavior, boundaries);
                (render.json() ? System.err : System.out).print(rows);
            }
            if (strict && report.pendingRows() > 0) {
                System.err.println(report.pendingRows() + " example row(s) are waiting for a `let`");
                System.exit(1);
            }
        } catch (CompileException e) {
            reportCompileError(e, sources, render);
            System.exit(1);
        } catch (IOException e) {
            System.err.println("io error: " + e.getMessage());
            System.exit(1);
        }
    }

    /** The level {@code --adequacy} names, or null where it names none. */
    private static Adequacy.Level adequacyLevel(String written) {
        return switch (written) {
            case "off" -> Adequacy.Level.OFF;
            case "witness" -> Adequacy.Level.WITNESS;
            case "all" -> Adequacy.Level.ALL;
            default -> null;
        };
    }

    /**
     * {@code souther fmt <file.sou>... [-w] [--check]}: rewrites each file into its canonical form
     * (see {@link Formatter}). With no flag the formatted source is printed to stdout; {@code -w}
     * writes it back in place; {@code --check} writes nothing and exits 1 if any file is not already
     * formatted, listing those files. A file with a syntax error is reported and left untouched.
     */
    private static void fmtSubcommand(String[] args) {
        boolean write = false;
        boolean check = false;
        List<Path> files = new ArrayList<>();
        for (String a : args) {
            switch (a) {
                case "-w", "--write" -> write = true;
                case "--check" -> check = true;
                default -> files.add(Path.of(a));
            }
        }
        if (files.isEmpty()) {
            System.err.println("fmt takes at least one .sou file");
            System.err.println(USAGE);
            System.exit(2);
            return;
        }
        if (write && check) {
            System.err.println("`-w` and `--check` are mutually exclusive");
            System.exit(2);
            return;
        }
        if (!write && !check && files.size() > 1) {
            // Concatenating several files to stdout gives an unattributable blob; make the intent explicit.
            System.err.println("formatting multiple files needs `-w` (write in place) or `--check`");
            System.exit(2);
            return;
        }
        List<Path> unformatted = new ArrayList<>();
        boolean failed = false;
        for (Path file : files) {
            String source;
            try {
                source = Files.readString(file);
            } catch (IOException e) {
                System.err.println("io error: " + file + ": " + e.getMessage());
                failed = true;
                continue;
            }
            CstParser.Result parsed = CstParser.parse(source);
            if (!parsed.errors().isEmpty()) {
                CstError first = parsed.errors().get(0);
                System.err.println(file + ": syntax error: " + first.legacyMessage());
                failed = true;
                continue;   // the formatter assumes a clean parse; leave a broken file untouched
            }
            String formatted = Formatter.format(parsed.root());
            if (check) {
                if (!formatted.equals(source)) {
                    unformatted.add(file);
                }
            } else if (write) {
                if (!formatted.equals(source)) {
                    try {
                        Files.writeString(file, formatted);
                    } catch (IOException e) {
                        System.err.println("io error: " + file + ": " + e.getMessage());
                        failed = true;
                    }
                }
            } else {
                System.out.print(formatted);
            }
        }
        if (check) {
            for (Path f : unformatted) {
                System.out.println(f);
            }
        }
        if (failed || (check && !unformatted.isEmpty())) {
            System.exit(1);
        }
    }

    /** {@code souther run <file.sou> [--behavior <name>] [--input <json>]}: compiles the file in
     * memory and drives one behavior, printing its output as JSON (see {@link Runner}). */
    private static void runSubcommand(String[] rawArgs) {
        RenderOptions render = new RenderOptions();
        String[] args = render.extract(rawArgs);
        Path source = firstSource(args);
        List<Path> sources = source == null ? List.of() : List.of(source);
        List<Located> warnings = new ArrayList<>();
        try {
            String output = Runner.runCli(args, warnings);
            // The warnings go to stderr and the behavior's output to stdout, so a caller piping the
            // result reads JSON and nothing else.
            report(warnings, sources, render);
            System.out.println(output);
        } catch (Runner.RunException e) {
            // The compile finished before the run began, so these warnings are the whole set — and a
            // run that aborted on an invariant is where a warning that the construction was unproven
            // is worth most. A usage error is raised before any of it and carries none.
            report(warnings, sources, render);
            System.err.println(e.localized(Messages.resolveLocale(render.lang)));
            System.exit(e.exitCode);
        } catch (CompileException e) {
            reportCompileError(e, sources, render);
            System.exit(1);
        }
    }

    /**
     * The file whose line the error should quote: the only source of a single-file compile, or — when
     * several were linked — the one the compiler was working on, which it tags the error with. Null
     * when a multi-file error names no source, so the snippet is left out rather than quoting a line
     * from the wrong file.
     */
    static Path sourceOf(List<Path> sources, CompileException e) {
        return sourceOf(sources, e, 0);
    }

    /** The file the {@code i}-th diagnostic should quote. */
    static Path sourceOf(List<Path> sources, CompileException e, int i) {
        return pathOf(sources, e.sourceIdOf(i));
    }

    /**
     * Which of the files handed over a source id names, or null when it names none of them.
     *
     * <p>A compile of one source names none, and the one file it was given is the answer however the
     * diagnostic is tagged — which is why one item is not read as "the source called 0, or nothing".
     */
    private static Path pathOf(List<Path> sources, String sourceId) {
        if (sources.size() == 1) {
            return sources.get(0);
        }
        for (int i = 0; i < sources.size(); i++) {
            if (Compilation.idOfSourceIndex(i).equals(sourceId)) {
                return sources.get(i);
            }
        }
        return null;
    }

    /** What to quote for each source a diagnostic points into, read once per file. */
    private static SourceContextResolver sourcesOf(List<Path> sources) {
        return SourceContextResolver.memoized(id -> read(pathOf(sources, id)));
    }

    /** A file as a snippet source, or null when it cannot be read — a snippet-less rendering is the
     *  honest fallback. */
    private static SourceContext read(Path source) {
        if (source == null) {
            return null;
        }
        try {
            return new SourceContext(source.getFileName().toString(), Files.readString(source));
        } catch (IOException _) {
            return null;
        }
    }

    /** Renders a compile error: an Elm-style snippet (or JSON) in the chosen locale, or the legacy
     * one-line form when the error is not yet structured. An error that carries several diagnostics
     * — every failing {@code example} row — prints each, so none of the reasons is lost. */
    private static void reportCompileError(CompileException e, List<Path> sources, RenderOptions render) {
        if (e.diagnostic() == null) {
            System.err.println(e.getMessage());
            return;
        }
        report(e.locatedDiagnostics(), sources, render);
    }

    /** Prints each diagnostic to stderr as the chosen renderer renders it, quoting the file it
     * belongs to. Errors and warnings take the same path; only where they come from differs. */
    private static void report(List<Located> located, List<Path> sources, RenderOptions render) {
        Locale locale = Messages.resolveLocale(render.lang);
        DiagnosticRenderer renderer = render.json()
                ? new JsonRenderer() : new HumanRenderer(render.useColor());
        for (String line : DiagnosticRenderer.renderAll(
                located, sourcesOf(sources), renderer, locale)) {
            System.err.println(line);
        }
    }

    /** The first non-option argument of {@code run} — the source file, for the error snippet. */
    private static Path firstSource(String[] args) {
        for (int i = 0; i < args.length; i++) {
            String a = args[i];
            if (a.equals("--behavior") || a.equals("--input")) {
                i++;
            } else if (!a.startsWith("--")) {
                return Path.of(a);
            }
        }
        return null;
    }

    /** Rendering flags shared by both subcommands, and the extraction that strips them out. */
    private static final class RenderOptions {
        private String format = "human";
        private String lang = null;
        private String color = "auto";

        boolean json() {
            return "json".equals(format);
        }

        boolean useColor() {
            return switch (color) {
                case "always" -> true;
                case "never" -> false;
                default -> System.console() != null && System.getenv("NO_COLOR") == null;
            };
        }

        String[] extract(String[] args) {
            List<String> kept = new ArrayList<>();
            for (int i = 0; i < args.length; i++) {
                switch (args[i]) {
                    case "--format" -> format = next(args, ++i);
                    case "--lang" -> lang = next(args, ++i);
                    case "--color" -> color = next(args, ++i);
                    default -> kept.add(args[i]);
                }
            }
            return kept.toArray(new String[0]);
        }

        private static String next(String[] args, int i) {
            if (i >= args.length) {
                System.err.println("option needs a value");
                System.err.println(USAGE);
                System.exit(2);
            }
            return args[i];
        }
    }

    /**
     * Compiles the given source files together — a single file, or several linked through their
     * imports (spec 4) — and writes each generated class under {@code outDir}. Returns the paths
     * written, in order.
     *
     * <p>This is the {@code compile} subcommand's own wiring, not a way to embed the compiler: it
     * hands its warnings to the caller to render rather than reporting them. Compiling from Java
     * goes through {@link Compiler} or the annotation processor, both of which say what they found.
     */
    static List<Path> compileToDir(List<Path> sources, Path outDir) throws IOException {
        return compileToDir(sources, outDir, List.of());
    }

    /**
     * As {@link #compileToDir(List, Path)}, resolving an import that names no module among
     * {@code sources} against the compiled modules on {@code classPath} — the directories and jars
     * of the projects this one depends on.
     */
    static List<Path> compileToDir(List<Path> sources, Path outDir, List<Path> classPath)
            throws IOException {
        return compileToDir(sources, outDir, classPath, new ArrayList<>());
    }

    /** As {@link #compileToDir(List, Path, List)}, collecting the compile's warnings into
     *  {@code warningsOut} for the caller to render — the CLI does, with the flags it was given. */
    static List<Path> compileToDir(List<Path> sources, Path outDir, List<Path> classPath,
                                   List<Located> warningsOut) throws IOException {
        return compileToDir(sources, outDir, classPath, warningsOut, Adequacy.Asked.NOTHING);
    }

    /** As above, warning about what the model's {@code example}s do not cover, at the level the
     * caller asked for. Off leaves the compile exactly as it was. */
    static List<Path> compileToDir(List<Path> sources, Path outDir, List<Path> classPath,
                                   List<Located> warningsOut, Adequacy.Asked measure)
            throws IOException {
        List<String> texts = new ArrayList<>();
        for (Path source : sources) {
            texts.add(Files.readString(source));
        }
        ModulePath path = classPath.isEmpty() ? ModulePath.EMPTY : ModulePath.ofClassPath(classPath);
        // A single header-less file is named after the file (F#/Elm; ADR-0043); a multi-file build
        // links by imports, so each must declare its own module header. One file that imports another
        // project's module is a module set of one, not a self-contained module.
        List<Located> compileWarnings = new ArrayList<>();
        Compilation compilation = texts.size() == 1 && classPath.isEmpty()
                ? Compiler.compiled(texts.get(0), Runner.moduleName(sources.get(0)),
                        compileWarnings, measure)
                : Compiler.compiledModules(texts, path, compileWarnings, measure);
        warningsOut.addAll(compileWarnings);
        Map<String, byte[]> classes = compilation.classes();
        List<Path> written = new ArrayList<>();
        for (Map.Entry<String, byte[]> entry : classes.entrySet()) {
            Path file = outDir.resolve(entry.getKey().replace('.', '/') + ".class");
            Files.createDirectories(file.getParent());
            Files.write(file, entry.getValue());
            written.add(file);
        }
        return written;
    }

    private Main() {}
}
