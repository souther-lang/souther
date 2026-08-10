package souther.compiler;

import java.util.EnumMap;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The options this command line takes, and what has to hold of a line that writes them.
 *
 * <p>Each command used to answer this for itself, out of the tokens it had a {@code case} for and a
 * default branch that read everything else as a path. That answers one question — is this token
 * mine — and only in the commands that thought to ask it: {@code doc} and {@code api} never did, so
 * {@code api Option --nope} ran as though nothing had been written. It also cannot answer the other
 * question at all. An option arrives as a local variable, and a local carries its value and not the
 * fact that somebody wrote it, so an option whose reader sits behind a condition that did not hold
 * is indistinguishable from one nobody asked for. {@code --boundaries} without {@code --generate}
 * was accepted, never read, and answered with the report it would have printed anyway.
 *
 * <p>So what a line wrote is kept as what it wrote — the set of options present, before any of them
 * is turned into a value — and the constraints are read off this table once, above the dispatch,
 * for every command. Three of them are structural and are written here: which command an option
 * belongs to, which other option it needs beside it, and which two may not be written together. The
 * fourth kind is not: whether an option's value makes the next one pointless (a colour under a JSON
 * renderer) is a question about what the values mean, which belongs to the command that means them.
 */
enum CliOption {

    FORMAT("compile/run/examples", Value.TAKEN, "--format"),
    LANG("compile/run/examples", Value.TAKEN, "--lang"),
    COLOR("compile/run/examples", Value.TAKEN, "--color"),
    CLASS_PATH("compile/run/examples/japi", Value.TAKEN, "-cp", "--class-path"),
    OUT_DIR("compile", Value.TAKEN, "-d"),
    ADEQUACY("compile", Value.TAKEN, "--adequacy"),
    WARNINGS("compile", Value.TAKEN, "--warnings"),
    BEHAVIOR("run/examples", Value.TAKEN, "--behavior"),
    INPUT("run", Value.TAKEN, "--input"),
    WRITE("fmt", Value.NONE, "-w", "--write"),
    CHECK("fmt", Value.NONE, "--check"),
    MODULE("examples", Value.TAKEN, "--module"),
    GENERATE("examples", Value.NONE, "--generate"),
    BOUNDARIES("examples", Value.NONE, "--boundaries"),
    STRICT("examples", Value.NONE, "--strict"),
    SEARCH("doc/api", Value.TAKEN, "--search"),
    LIMIT("doc", Value.TAKEN, "--limit"),
    SOURCE("api", Value.TAKEN, "--source");

    /** Whether the token after this one is its value or the next argument. */
    enum Value { NONE, TAKEN }

    /** Why a command line is refused: a catalog key and what fills it. */
    record Refusal(String key, Object... args) {}

    /**
     * What one reading of a command line found: why it is refused, if it is, and the language it is
     * to be answered in.
     *
     * <p>The two come from the same walk because they are answers about the same tokens. Reading the
     * line twice — once to find {@code --lang}, once to check it — is two rules for what a token is,
     * and they part company on the lines that need them most: a value that is spelt like an option
     * is a value to one walk and an option to the other.
     */
    record Reading(Refusal refusal, String lang) {}

    /**
     * The commands that take the option, in the form a refusal names them.
     *
     * <p>Not the commands it is documented under. The usage text groups an option under one heading
     * — {@code --behavior} under {@code examples} — and {@code run} takes it too; a refusal built
     * from the heading would send an author to the wrong command line.
     */
    private final String owners;

    private final Value value;

    /** Every spelling of the option, the first of which is the one a refusal names it by. */
    private final List<String> spellings;

    CliOption(String owners, Value value, String... spellings) {
        this.owners = owners;
        this.value = value;
        this.spellings = List.of(spellings);
    }

    /**
     * What each option needs written beside it.
     *
     * <p>The usage text has said this all along — {@code [--generate [--boundaries]]}, {@code doc
     * --search <term> [--limit <n>]} — as a nesting of brackets, which is a statement no program
     * reads. Here it is the same statement in the form the check is made from.
     */
    private static final Map<CliOption, CliOption> NEEDS = new EnumMap<>(Map.of(
            BOUNDARIES, GENERATE,
            LIMIT, SEARCH));

    /**
     * The pairs no line may write together, each declared once and read both ways round. Written as
     * a pair rather than as a field on either option, because a conflict is a fact about the two of
     * them and stating it twice is two things to keep in step.
     */
    private static final List<Set<CliOption>> EXCLUSIVE = List.of(EnumSet.of(WRITE, CHECK));

    private static final Map<String, CliOption> BY_SPELLING = spellingIndex();

    private static Map<String, CliOption> spellingIndex() {
        Map<String, CliOption> index = new LinkedHashMap<>();
        for (CliOption option : values()) {
            for (String spelling : option.spellings) {
                index.put(spelling, option);
            }
        }
        return Map.copyOf(index);
    }

    /** Every spelling this compiler knows, in the order the table writes them. */
    static Set<String> spellings() {
        return new LinkedHashSet<>(BY_SPELLING.keySet());
    }

    /** The commands that take the option written this way, or null where this compiler has none. */
    static String owners(String spelling) {
        CliOption option = BY_SPELLING.get(spelling);
        return option == null ? null : option.owners;
    }

    private boolean ownedBy(String command) {
        for (String owner : owners.split("/")) {
            if (owner.equals(command)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Why this command may not be run as written, or null where nothing on the line refuses it.
     *
     * <p>Asked before the command is dispatched, so the answer is the same one whichever command was
     * named, and a command written after this one is under it without having to remember to be.
     *
     * <p>A token reading as an option is a token beginning {@code --}: a bare {@code --} is one, and
     * is refused as an option nobody has. A single dash is not, which is the rule {@code run} has
     * always had — a file may be named {@code -d} and a command that has no {@code -d} still reads it
     * as one. That makes the short options command-scoped: {@code fmt} knows {@code -w} and
     * {@code compile} reads the same token as a path.
     */
    static Reading read(String command, String[] args) {
        EnumSet<CliOption> written = EnumSet.noneOf(CliOption.class);
        Map<CliOption, String> asWritten = new EnumMap<>(CliOption.class);
        Refusal token = null;
        String lang = null;
        for (int i = 0; i < args.length; i++) {
            String word = args[i];
            CliOption option = BY_SPELLING.get(word);
            if (option == null) {
                if (word.startsWith("--") && token == null) {
                    token = new Refusal("cli.option.unknown", word, command);
                }
                continue;   // a source file, a name, or a short option this compiler has no such
            }
            if (!option.ownedBy(command)) {
                if (word.startsWith("--") && token == null) {
                    token = new Refusal("cli.option.foreign", word, command, option.owners);
                }
                continue;   // a short option this command does not know still reads as a path
            }
            written.add(option);
            asWritten.put(option, word);
            if (option.value == Value.TAKEN) {
                // Whatever follows is this option's value, option-shaped or not: `--module
                // --generate` names a module, which is what the command's own parser reads it as.
                if (++i >= args.length) {
                    // And an option written last has no value at all. Answered here rather than
                    // where each one is read: `--limit` is read inside a loop that skipped it when
                    // nothing followed, so `doc --search newtype --limit` searched under the
                    // default and said nothing — the same silence as an option nobody reads.
                    if (token == null) {
                        token = new Refusal("cli.option.value", word);
                    }
                    break;
                }
                if (option == LANG) {
                    lang = args[i];   // the last one written, which is the one the parsers read
                }
            }
        }
        return new Reading(token != null ? token : unmet(written, asWritten), lang);
    }

    /** The first constraint between options this line does not meet, or null where it meets them. */
    private static Refusal unmet(Set<CliOption> written, Map<CliOption, String> asWritten) {
        for (CliOption option : written) {
            CliOption needed = NEEDS.get(option);
            if (needed != null && !written.contains(needed)) {
                return new Refusal("cli.option.needs",
                        asWritten.get(option), needed.spellings.get(0));
            }
        }
        for (Set<CliOption> pair : EXCLUSIVE) {
            if (written.containsAll(pair)) {
                List<CliOption> both = List.copyOf(pair);
                return new Refusal("cli.option.exclusive",
                        asWritten.get(both.get(0)), asWritten.get(both.get(1)));
            }
        }
        return null;
    }

    /** Whether the token after this one is read as its value. */
    static boolean takesValue(String spelling) {
        CliOption option = BY_SPELLING.get(spelling);
        return option != null && option.value == Value.TAKEN;
    }

    /** What the option needs written beside it, or null where it stands on its own. */
    static String needed(String spelling) {
        CliOption option = BY_SPELLING.get(spelling);
        CliOption needs = option == null ? null : NEEDS.get(option);
        return needs == null ? null : needs.spellings.get(0);
    }

    /** The pairs no command line may write together, as the spellings a refusal names them by. */
    static List<List<String>> exclusive() {
        List<List<String>> pairs = new java.util.ArrayList<>();
        for (Set<CliOption> pair : EXCLUSIVE) {
            List<String> spelt = new java.util.ArrayList<>();
            for (CliOption option : pair) {
                spelt.add(option.spellings.get(0));
            }
            pairs.add(List.copyOf(spelt));
        }
        return List.copyOf(pairs);
    }
}
