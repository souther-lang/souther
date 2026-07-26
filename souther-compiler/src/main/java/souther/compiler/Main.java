package souther.compiler;

import souther.compiler.cst.CstError;
import souther.compiler.cst.CstParser;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.JsonRenderer;
import souther.compiler.diag.Messages;
import souther.compiler.diag.SourceContext;
import souther.compiler.fmt.Formatter;

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
              compile <file.sou>... -d <outdir>                    compile to .class files
              run <file.sou> [--behavior <name>] [--input <json>]  run a behavior, print its output
              fmt <file.sou>... [-w] [--check]                     format source (stdout, or -w in place)
            options (compile/run):
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
        Path outDir = Path.of(".");
        for (int i = 0; i < args.length; i++) {
            if (args[i].equals("-d")) {
                if (++i >= args.length) {
                    System.err.println("`-d` needs an output directory");
                    System.err.println(USAGE);
                    System.exit(2);
                    return;
                }
                outDir = Path.of(args[i]);
            } else {
                sources.add(Path.of(args[i]));
            }
        }
        if (sources.isEmpty()) {
            System.err.println("compile takes at least one .sou file");
            System.err.println(USAGE);
            System.exit(2);
            return;
        }
        try {
            for (Path file : compileToDir(sources, outDir)) {
                System.out.println("wrote " + file);
            }
        } catch (CompileException e) {
            reportCompileError(e, sourceOf(sources, e), render);
            System.exit(1);
        } catch (IOException e) {
            System.err.println("io error: " + e.getMessage());
            System.exit(1);
        }
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
        try {
            System.out.println(Runner.runCli(args));
        } catch (Runner.RunException e) {
            System.err.println(e.localized(Messages.resolveLocale(render.lang)));
            System.exit(e.exitCode);
        } catch (CompileException e) {
            reportCompileError(e, firstSource(args), render);
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
        if (sources.size() == 1) {
            return sources.get(0);
        }
        int index = e.sourceIndex();
        return index >= 0 && index < sources.size() ? sources.get(index) : null;
    }

    /** Renders a compile error: an Elm-style snippet (or JSON) in the chosen locale, or the legacy
     * one-line form when the error is not yet structured. */
    private static void reportCompileError(CompileException e, Path source, RenderOptions render) {
        Diagnostic d = e.diagnostic();
        if (d == null) {
            System.err.println(e.getMessage());
            return;
        }
        SourceContext src = null;
        if (source != null) {
            try {
                src = new SourceContext(source.getFileName().toString(), Files.readString(source));
            } catch (IOException ignore) {
                // Fall back to a snippet-less rendering.
            }
        }
        Locale locale = Messages.resolveLocale(render.lang);
        DiagnosticRenderer renderer = render.json()
                ? new JsonRenderer() : new HumanRenderer(render.useColor());
        System.err.println(renderer.render(d, src, locale));
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
     */
    public static List<Path> compileToDir(List<Path> sources, Path outDir) throws IOException {
        List<String> texts = new ArrayList<>();
        for (Path source : sources) {
            texts.add(Files.readString(source));
        }
        // A single header-less file is named after the file (F#/Elm; ADR-0043); a multi-file build
        // links by imports, so each must declare its own module header.
        Compiler.Compiled compiled = texts.size() == 1
                ? Compiler.compileWithWarnings(texts.get(0), Runner.moduleName(sources.get(0)))
                : Compiler.compileModulesWithWarnings(texts);
        for (Diagnostic w : compiled.warnings()) {
            System.err.println("warning: " + DiagnosticRenderer.body(w, Locale.ENGLISH));
        }
        Map<String, byte[]> classes = compiled.classes();
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
