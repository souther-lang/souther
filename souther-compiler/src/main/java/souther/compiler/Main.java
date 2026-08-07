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
import souther.compiler.diag.SourceNames;
import souther.compiler.doc.ApiCommand;
import souther.compiler.doc.DocCommand;
import souther.compiler.doc.JapiCommand;
import souther.compiler.doc.McpServer;
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
              fmt <file.sou>... [-w|--write] [--check]             format source (stdout, or -w in place)
              examples <file.sou>... [-cp <path>]                  how well the `example`s cover the model
              doc [<anchor> | <error-code> | <set>/<topic> | --search <term>]  read the language specification
              api [<Module>[.<name>] | --search <term>]            the stdlib surface and its signatures
              japi <class-or-package>[#<member>] [-cp <path>]      a dependency jar's public API, with javadoc
            options (doc):
              --search <term>           sections and topics that say the term, best answer first
              --limit <n>               how many hits to show (default 20; 0 for all of them)
            options (api):
              --source <Module>         a stdlib module's own source, design comments included
              mcp                                                  serve doc/api/japi over MCP stdio
            options (examples):
              --module <name>           report only this module
              --behavior <name>         report only this behavior
              --generate                print commented rows for what nothing covers
              --boundaries              with --generate, add rows at the untried boundaries
              --strict                  exit non-zero while rows are waiting for a `let`
            options (compile):
              --adequacy off|witness|all  warn about what the `example`s do not cover (default off)
              --warnings report|error   refuse a compile that warns (default report)
            options (compile/examples/japi):
              -cp, --class-path <path>  where to find modules another project compiled

            options (compile/run/examples):
              --format human|json      how to render a compile error (default: human)
              --lang <tag>             message locale, e.g. ja or en
                                       (overrides SOUTHER_LANG; with neither, en)
              --color auto|always|never  color the human output (default: auto)""";

    /**
     * Which commands take each option: what a command reads when it has to say that an option is
     * not its own but is somebody's.
     *
     * <p>Written here rather than read back out of {@link #USAGE}. The usage text is what an author
     * is shown, and reading it for what an option means is the dependency the wrong way round — it
     * says an option under the heading of the commands it is documented with, which is not the same
     * set as the commands that accept it. {@code --behavior} is documented under {@code examples}
     * and taken by {@code run} as well; {@code -cp} is documented under {@code compile/examples} and
     * taken by {@code japi} too. This table is the one the commands answer from, and a test holds it
     * against both the usage text and what each parser has a case for.
     */
    private static final Map<String, String> OPTION_OWNERS = Map.ofEntries(
            Map.entry("--format", "compile/run/examples"),
            Map.entry("--lang", "compile/run/examples"),
            Map.entry("--color", "compile/run/examples"),
            Map.entry("-cp", "compile/examples/japi"),
            Map.entry("--class-path", "compile/examples/japi"),
            Map.entry("-d", "compile"),
            Map.entry("--adequacy", "compile"),
            Map.entry("--warnings", "compile"),
            Map.entry("--behavior", "run/examples"),
            Map.entry("--input", "run"),
            Map.entry("-w", "fmt"),
            Map.entry("--write", "fmt"),
            Map.entry("--check", "fmt"),
            Map.entry("--module", "examples"),
            Map.entry("--generate", "examples"),
            Map.entry("--boundaries", "examples"),
            Map.entry("--strict", "examples"),
            Map.entry("--search", "doc/api"),
            Map.entry("--limit", "doc"),
            Map.entry("--source", "api"));

    /** Every option this table names, for the test that holds it against the usage text. */
    static java.util.Set<String> knownOptions() {
        return OPTION_OWNERS.keySet();
    }

    /** The usage text, for the test that holds it against the table. */
    static String usage() {
        return USAGE;
    }

    /** The commands that take {@code option}, or null where this compiler has no such option. */
    static String optionOwners(String option) {
        return OPTION_OWNERS.get(option);
    }

    /**
     * Whether the token reads as an option rather than as a path.
     *
     * <p>What {@code run} has always asked, now asked by the commands that were not asking it. A
     * short option a command does not know still reads as a path, which is where {@code run} draws
     * the line too. A bare {@code --} reads as an option and is refused as an unknown one; no command
     * takes it as the end of its options yet.
     */
    private static boolean looksLikeOption(String arg) {
        return arg.startsWith("--");
    }

    /** The usage error a command answers with when a token reads as an option it has no case for. */
    private static int unknownOption(String command, String option) {
        String owners = OPTION_OWNERS.get(option);
        System.err.println("unknown option `" + option + "` for `" + command + "`"
                + (owners == null ? "" : " — it is an option of " + owners));
        System.err.println(USAGE);
        return 2;
    }

    public static void main(String[] args) {
        int code = guarded(() -> dispatch(args));
        if (code != 0) {
            System.exit(code);
        }
    }

    /**
     * Runs the command with the last boundary this compiler has around it, and answers with the exit
     * code.
     *
     * <p>Around the whole command and not around the compile inside it: reading the arguments builds
     * paths and options, and a failure there is as much this compiler's as one from the emitter. A
     * {@link CompileException} is not one of these — it is an answer about the source and is rendered
     * as one where it is caught — so it goes on rather than being reported as a fault of the compiler.
     */
    static int guarded(java.util.function.IntSupplier command) {
        try {
            return command.getAsInt();
        } catch (RuntimeException e) {
            String said = internalFailure(e);
            if (said == null) {
                throw e;
            }
            System.err.println(said);
            return 1;
        }
    }

    /**
     * The command's answer as its exit code, which only {@link #main} turns into one.
     *
     * <p>Ending the process is a fact about the process, not about the command, and a command that
     * ends it has no answer left to give: everything it decides — that an option is not one of its
     * own, that a file is not formatted — is unreachable from anywhere but a shell. Read as a number
     * here, each of those is an ordinary result.
     */
    static int dispatch(String[] args) {
        String command = args.length == 0 ? "" : args[0];
        String[] rest = args.length == 0 ? args : java.util.Arrays.copyOfRange(args, 1, args.length);
        return switch (command) {
            case "run" -> runSubcommand(rest);
            case "compile" -> compileSubcommand(rest);
            case "fmt" -> fmtSubcommand(rest);
            case "examples" -> examplesSubcommand(rest);
            case "doc" -> DocCommand.run(rest, System.out, System.err);
            case "api" -> ApiCommand.run(rest, System.out, System.err);
            case "japi" -> JapiCommand.run(rest, System.out, System.err);
            case "mcp" -> McpServer.serve(System.in, System.out);
            default -> {
                String hint = command.endsWith(".sou")
                        ? "no command given — did you mean `souther compile " + command
                                + " …` or `souther run " + command + " …`?"
                        : command.isEmpty() ? "no command given" : "unknown command `" + command + "`";
                System.err.println(hint);
                System.err.println(USAGE);
                yield 2;
            }
        };
    }

    /**
     * The one line the command line says when the compiler fails for a reason nobody listed, or
     * {@code null} for a {@link CompileException}, which is an answer about the source and is
     * rendered as one wherever it is caught.
     *
     * <p>A stack trace at this point asks the author to read this compiler's call stack for a problem
     * that is not theirs. What is left — the exception's name and what it said — is what a report of
     * it would be filed with, and is the only part of it they can pass on.
     */
    static String internalFailure(RuntimeException e) {
        if (e instanceof CompileException) {
            return null;
        }
        String said = e.getMessage();
        return "internal compiler error: " + e.getClass().getSimpleName()
                + (said == null ? "" : ": " + said.replaceAll("\\R", " "));
    }

    /** {@code souther compile <file.sou>... -d <outdir>}: writes the generated {@code .class} files. */
    private static int compileSubcommand(String[] rawArgs) {
        RenderOptions render = new RenderOptions();
        String[] args = render.extract(rawArgs);
        if (args == null) {
            return 2;
        }
        List<Path> sources = new ArrayList<>();
        List<Path> classPath = new ArrayList<>();
        Path outDir = Path.of(".");
        Adequacy.Asked measure = Adequacy.Asked.NOTHING;
        boolean refuseWarnings = false;
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--adequacy" -> {
                    if (++i >= args.length || adequacyLevel(args[i]) == null) {
                        System.err.println("`--adequacy` takes off, witness or all");
                        return 2;
                    }
                    measure = Adequacy.Asked.warningsAt(adequacyLevel(args[i]));
                }
                case "--warnings" -> {
                    if (++i >= args.length
                            || !(args[i].equals("report") || args[i].equals("error"))) {
                        System.err.println("`--warnings` takes report or error");
                        return 2;
                    }
                    refuseWarnings = args[i].equals("error");
                }
                case "-d" -> {
                    if (++i >= args.length) {
                        System.err.println("`-d` needs an output directory");
                        System.err.println(USAGE);
                        return 2;
                    }
                    outDir = Path.of(args[i]);
                }
                case "-cp", "--class-path" -> {
                    if (++i >= args.length) {
                        System.err.println("`" + args[i - 1] + "` needs a class path");
                        System.err.println(USAGE);
                        return 2;
                    }
                    for (String entry : args[i].split(java.io.File.pathSeparator)) {
                        if (!entry.isBlank()) {
                            classPath.add(Path.of(entry));
                        }
                    }
                }
                default -> {
                    if (looksLikeOption(args[i])) {
                        return unknownOption("compile", args[i]);
                    }
                    sources.add(Path.of(args[i]));
                }
            }
        }
        if (sources.isEmpty()) {
            System.err.println("compile takes at least one .sou file");
            System.err.println(USAGE);
            return 2;
        }
        List<Located> warnings = new ArrayList<>();
        try {
            Map<String, byte[]> classes = compiledClasses(sources, classPath, warnings, measure);
            // Before the written files: the warnings are about the source, and a long list of paths
            // between them and the command would bury them.
            report(warnings, sources, render);
            if (refuseWarnings && !warnings.isEmpty()) {
                return refused(render);
            }
            for (Path file : writeClasses(classes, outDir)) {
                System.out.println("wrote " + file);
            }
            return 0;
        } catch (CompileException e) {
            reportCompileError(e, sources, render);
            return 1;
        } catch (IOException e) {
            // The compile itself finished — these warnings are the whole set, and what stopped the
            // command was writing the classes out, which says nothing about the source.
            report(warnings, sources, render);
            System.err.println("io error: " + e.getMessage());
            return 1;
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
    private static int examplesSubcommand(String[] rawArgs) {
        RenderOptions render = new RenderOptions();
        String[] args = render.extract(rawArgs);
        if (args == null) {
            return 2;
        }
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
                        return 2;
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
                        return 2;
                    }
                    module = Reserved.name(args[i]);   // a name from outside
                }
                case "--behavior" -> {
                    if (++i >= args.length) {
                        System.err.println("`--behavior` needs a behavior name");
                        return 2;
                    }
                    behavior = Reserved.name(args[i]);   // a name from outside
                }
                case "--generate" -> generate = true;
                case "--boundaries" -> boundaries = true;
                case "--strict" -> strict = true;
                default -> {
                    if (looksLikeOption(args[i])) {
                        return unknownOption("examples", args[i]);
                    }
                    sources.add(Path.of(args[i]));
                }
            }
        }
        if (sources.isEmpty()) {
            System.err.println("examples takes at least one .sou file");
            System.err.println(USAGE);
            return 2;
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
                return 1;
            }
            return 0;
        } catch (CompileException e) {
            reportCompileError(e, sources, render);
            return 1;
        } catch (IOException e) {
            System.err.println("io error: " + e.getMessage());
            return 1;
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
    private static int fmtSubcommand(String[] args) {
        boolean write = false;
        boolean check = false;
        List<Path> files = new ArrayList<>();
        for (String a : args) {
            switch (a) {
                case "-w", "--write" -> write = true;
                case "--check" -> check = true;
                default -> {
                    if (looksLikeOption(a)) {
                        return unknownOption("fmt", a);
                    }
                    files.add(Path.of(a));
                }
            }
        }
        if (files.isEmpty()) {
            System.err.println("fmt takes at least one .sou file");
            System.err.println(USAGE);
            return 2;
        }
        if (write && check) {
            System.err.println("`-w` and `--check` are mutually exclusive");
            return 2;
        }
        if (!write && !check && files.size() > 1) {
            // Concatenating several files to stdout gives an unattributable blob; make the intent explicit.
            System.err.println("formatting multiple files needs `-w` (write in place) or `--check`");
            return 2;
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
            String formatted;
            try {
                CstParser.Result parsed = CstParser.parse(source);
                if (!parsed.errors().isEmpty()) {
                    CstError first = parsed.errors().get(0);
                    System.err.println(file + ": syntax error: " + first.legacyMessage());
                    failed = true;
                    continue;   // the formatter assumes a clean parse; leave a broken file untouched
                }
                formatted = Formatter.format(parsed.root());
            } catch (CompileException e) {
                // One file this command cannot read must cost that file, not the run and not the
                // author's screen. Reading is a walk down the source and a walk down the tree it
                // made, and either can find a limit; a `fmt` that answered those with a stack trace
                // told the author about the compiler rather than about their file.
                System.err.println(file + ": " + e.getMessage());
                failed = true;
                continue;
            } catch (RuntimeException e) {
                System.err.println(file + ": " + internalFailure(e));
                failed = true;
                continue;
            }
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
        return failed || (check && !unformatted.isEmpty()) ? 1 : 0;
    }

    /** {@code souther run <file.sou> [--behavior <name>] [--input <json>]}: compiles the file in
     * memory and drives one behavior, printing its output as JSON (see {@link Runner}). */
    private static int runSubcommand(String[] rawArgs) {
        RenderOptions render = new RenderOptions();
        String[] args = render.extract(rawArgs);
        if (args == null) {
            return 2;
        }
        Path source = firstSource(args);
        List<Path> sources = source == null ? List.of() : List.of(source);
        List<Located> warnings = new ArrayList<>();
        try {
            String output = Runner.runCli(args, warnings);
            // The warnings go to stderr and the behavior's output to stdout, so a caller piping the
            // result reads JSON and nothing else.
            report(warnings, sources, render);
            System.out.println(output);
            return 0;
        } catch (Runner.RunException e) {
            // The compile finished before the run began, so these warnings are the whole set — and a
            // run that aborted on an invariant is where a warning that the construction was unproven
            // is worth most. A usage error is raised before any of it and carries none.
            report(warnings, sources, render);
            System.err.println(e.localized(Messages.resolveLocale(render.lang)));
            return e.exitCode;
        } catch (CompileException e) {
            reportCompileError(e, sources, render);
            return 1;
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
        int at = indexOf(sources, sourceId);
        return at < 0 ? null : sources.get(at);
    }

    /** What to quote for each source a diagnostic points into, read once per file, under names no
     *  two of these files share. */
    private static SourceContextResolver sourcesOf(List<Path> sources) {
        List<String> names = SourceNames.of(sources.stream().map(Path::toString).toList());
        return SourceContextResolver.memoized(id -> {
            int at = indexOf(sources, id);
            return at < 0 ? null : read(sources.get(at), names.get(at));
        });
    }

    /** Which of the files handed over a source id names, or -1 when it names none of them. */
    private static int indexOf(List<Path> sources, String sourceId) {
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

    /** A file as a snippet source under the name a reader is shown it by, or null when it cannot be
     *  read — a snippet-less rendering is the honest fallback. */
    private static SourceContext read(Path source, String name) {
        if (source == null) {
            return null;
        }
        try {
            return new SourceContext(name, Files.readString(source));
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

    /**
     * Says that the warnings just printed are what stopped this build, and answers with the exit code
     * for it.
     *
     * <p>Not under {@code --format json}. What that format writes is one object per diagnostic with
     * nothing around them, so a reader takes the output a line at a time; a sentence among them is a
     * line that parses as nothing, and a reader given it cannot tell that from output it should have
     * understood. There the exit code is what says it, which is what a tool reads anyway.
     */
    private static int refused(RenderOptions render) {
        if (!render.json()) {
            System.err.println(Messages.get("cli.warnings.refused",
                    Messages.resolveLocale(render.lang)));
        }
        return 1;
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

        /** The arguments with these flags taken out, or {@code null} where one of them was written
         *  without its value — which the caller answers as a usage error. */
        String[] extract(String[] args) {
            List<String> kept = new ArrayList<>();
            for (int i = 0; i < args.length; i++) {
                String option = args[i];
                switch (option) {
                    case "--format", "--lang", "--color" -> {
                        if (++i >= args.length) {
                            System.err.println("`" + option + "` needs a value");
                            System.err.println(USAGE);
                            return null;
                        }
                        switch (option) {
                            case "--format" -> format = args[i];
                            case "--lang" -> lang = args[i];
                            default -> color = args[i];
                        }
                    }
                    default -> kept.add(option);
                }
            }
            return kept.toArray(new String[0]);
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
        return writeClasses(compiledClasses(sources, classPath, warningsOut, measure), outDir);
    }

    /**
     * The classes the sources compile to, by binary name, with the compile's warnings collected into
     * {@code warningsOut}.
     *
     * <p>Held apart from writing them because a command may read the warnings before deciding whether
     * this build is one it accepts, and a build it does not accept writes nothing: the exit code says
     * the classes are not the output of an accepted compile, and a directory holding them anyway is
     * what a later step would read as if they were.
     */
    static Map<String, byte[]> compiledClasses(List<Path> sources, List<Path> classPath,
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
        return compilation.classes();
    }

    /** Writes each class under {@code outDir}, and answers with the paths written, in order. */
    static List<Path> writeClasses(Map<String, byte[]> classes, Path outDir) throws IOException {
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
