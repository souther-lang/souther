package souther.cli;

import java.util.Collections;
import java.util.EnumMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The commands this command line has, and what each one is for.
 *
 * <p>The one place a command name is resolved. The dispatch used to name them in a {@code switch}
 * over strings and the usage text named them again in prose, so a command was two statements that
 * agreed by hand: the text said {@code mcp} was an option of {@code api} for as long as nobody
 * read it against anything. A name resolves to a constant here and the dispatch switches over the
 * constants, so a command added to this table and left undispatched is a build that does not
 * compile rather than a drift a test has to go looking for.
 *
 * <p>{@code help} is one of them and not a shape the dispatch knows about. It is a command an author
 * writes like any other, so it has what the others have — arguments it takes, a line saying what it
 * is for, and a section of its own that {@code souther help help} answers with. A meta-command
 * special-cased above the table would be the one command unable to explain itself.
 *
 * <p>What a command takes is not written here. {@link CliOption} says which commands each option
 * belongs to, and a section is built by asking it; the only thing this table says about an option
 * is what it means <em>under this command</em>, where that differs from what the option means on
 * its own.
 */
enum CliCommand {

    INIT("init", "[<groupId>:<artifactId>]", "start a project, or add Souther to one",
            Scope.INDEPENDENT,
            Map.of(CliOption.MODULE,
                    "the `.sou` module header (default: the coordinate)",
                    CliOption.DIRECTORY,
                    "where to write it (default: the artifactId, or here when adding)")),
    COMPILE("compile", "<file.sou>...", "compile to .class files, or for an installed target",
            Scope.PROJECT,
            Map.of(CliOption.DIRECTORY, "where the generated .class files are written"),
            new Also(List.of("--target <target> <target-arguments>..."),
                    List.of("`--target` is read only as the first argument. `jvm` is built in and"
                            + " is what a line without it means. Any other target is an"
                            + " installed backend, and everything after its name is the"
                            + " backend's own: `souther compile --target <target> --help` asks"
                            + " it what it takes."))),
    RUN("run", "<file.sou>", "run one behavior and print its output", Scope.PROJECT,
            Map.of(CliOption.BEHAVIOR, "which behavior to run (default: the only one)")),
    FMT("fmt", "<file.sou>...", "format source, to stdout or in place", Scope.PROJECT),
    EXAMPLES("examples", "<file.sou>...", "how well the `example`s cover the model",
            Scope.PROJECT,
            Map.of(CliOption.FORMAT, "how to render the report, and any compile "
                    + "error (default human)")),
    DOC("doc", "[<anchor> | <error-code> | <set>/<topic>[/<section>]]",
            "read the language specification", Scope.INDEPENDENT),
    API("api", "[<Module>[.<name>]]", "the stdlib surface and its signatures",
            Scope.INDEPENDENT,
            Map.of(CliOption.SEARCH, "the published names whose signature or "
                    + "document says the term")),
    JAPI("japi", "<class-or-package>[#<member>]", "a dependency jar's public API, with javadoc",
            Scope.INDEPENDENT,
            Map.of(CliOption.CLASS_PATH, "where to find the jar to read")),
    MCP("mcp", "", "serve doc, api and japi over MCP stdio", Scope.INDEPENDENT),
    LSP("lsp", "", "serve the language server over LSP stdio", Scope.INDEPENDENT),
    TOOLING("tooling", "", "what an editor needs to start and configure the server, as JSON",
            Scope.INDEPENDENT),
    HELP("help", "[<command>]", "what a command takes, and what its options mean",
            Scope.INDEPENDENT),
    VERSION("version", "", "which Souther this is", Scope.INDEPENDENT);

    /**
     * Whether a command is about a project, and so held to the Souther the project says it needs.
     *
     * <p>A fact of the command and stated beside it. Asking of a run whether it turned out to read
     * a project would make the answer depend on what the command's arguments mean, which for a
     * command that hands them to something else is not the CLI's to know.
     */
    enum Scope {
        /** Reads or writes a project's sources, and is refused under another Souther's version. */
        PROJECT,
        /** Answers about this Souther, or starts a project, and is the same wherever it is run. */
        INDEPENDENT
    }

    private static final Map<String, CliCommand> BY_SPELLING = spellingIndex();

    private static Map<String, CliCommand> spellingIndex() {
        Map<String, CliCommand> index = new LinkedHashMap<>();
        for (CliCommand command : values()) {
            index.put(command.spelling, command);
        }
        return Map.copyOf(index);
    }

    private final String spelling;

    /** What this command takes besides its options, in the form a synopsis writes them. */
    private final String operands;

    /** What this command is for, in one line. */
    private final String summary;

    /** What an option of this command's means here, where that is not what it means on its own. */
    private final Map<CliOption, String> reads;

    /** Whether the Souther a project names is the Souther this command runs under. */
    private final Scope scope;

    /** The other ways this command is written, and what a reader is told about them. */
    private final Also also;

    /**
     * The other forms a command is written in, and what is said about them.
     *
     * <p>{@code forms} are synopses after the command's name, one for each form besides the one
     * {@code operands} states; {@code notes} are sentences written under the options.
     */
    record Also(List<String> forms, List<String> notes) {
        static final Also NONE = new Also(List.of(), List.of());
    }

    CliCommand(String spelling, String operands, String summary, Scope scope) {
        this(spelling, operands, summary, scope, Map.of(), Also.NONE);
    }

    CliCommand(String spelling, String operands, String summary, Scope scope,
               Map<CliOption, String> reads) {
        this(spelling, operands, summary, scope, reads, Also.NONE);
    }

    CliCommand(String spelling, String operands, String summary, Scope scope,
               Map<CliOption, String> reads, Also also) {
        this.spelling = spelling;
        this.operands = operands;
        this.summary = summary;
        this.scope = scope;
        this.also = also;
        // Held unmodifiable, which is what a field of an enum constant has to be: every caller of
        // this command sees the one map, so a caller that could write to it would be writing for
        // all of them.
        this.reads = reads.isEmpty() ? Map.of()
                : Collections.unmodifiableMap(new EnumMap<>(reads));
    }

    /** The command this name is, or null where this compiler has no such command. */
    static CliCommand named(String name) {
        return BY_SPELLING.get(name);
    }

    String spelling() {
        return spelling;
    }

    String operands() {
        return operands;
    }

    String summary() {
        return summary;
    }

    Scope scope() {
        return scope;
    }

    Also also() {
        return also;
    }

    /**
     * What the option means under this command.
     *
     * <p>This command's own reading where it has one, and the option's otherwise. The same spelling
     * is read differently by commands that ask different questions with it — {@code --behavior}
     * chooses what {@code run} runs and narrows what {@code examples} reports on, and {@code -cp}
     * is where {@code compile} finds modules and where {@code japi} finds a jar — and a section
     * that printed one sentence under both would be documenting the spelling rather than the
     * option.
     */
    String describe(CliOption option) {
        return reads.getOrDefault(option, option.description());
    }
}
