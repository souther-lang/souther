package souther.compiler;

import java.util.EnumMap;
import java.util.LinkedHashMap;
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

    COMPILE("compile", "<file.sou>...", "compile to .class files"),
    RUN("run", "<file.sou>", "run one behavior and print its output",
            Map.of(CliOption.BEHAVIOR, "which behavior to run (default: the only one)")),
    FMT("fmt", "<file.sou>...", "format source, to stdout or in place"),
    EXAMPLES("examples", "<file.sou>...", "how well the `example`s cover the model",
            Map.of(CliOption.FORMAT, "how to render the report, and any compile error "
                    + "(default human)")),
    DOC("doc", "[<anchor> | <error-code> | <set>/<topic>[/<section>]]",
            "read the language specification"),
    API("api", "[<Module>[.<name>]]", "the stdlib surface and its signatures",
            Map.of(CliOption.SEARCH, "the published names whose signature or document says the "
                    + "term")),
    JAPI("japi", "<class-or-package>[#<member>]", "a dependency jar's public API, with javadoc",
            Map.of(CliOption.CLASS_PATH, "where to find the jar to read")),
    MCP("mcp", "", "serve doc, api and japi over MCP stdio"),
    HELP("help", "[<command>]", "what a command takes, and what its options mean");

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

    CliCommand(String spelling, String operands, String summary) {
        this(spelling, operands, summary, Map.of());
    }

    CliCommand(String spelling, String operands, String summary, Map<CliOption, String> reads) {
        this.spelling = spelling;
        this.operands = operands;
        this.summary = summary;
        this.reads = reads.isEmpty() ? Map.of() : new EnumMap<>(reads);
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
        String read = reads.get(option);
        return read != null ? read : option.description();
    }
}
