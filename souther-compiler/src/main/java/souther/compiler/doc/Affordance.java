package souther.compiler.doc;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * An operation a document sends its reader to, written in the document as what it does rather than
 * as how one caller spells it.
 *
 * <p>Prose carries two kinds of mention. One states what a command is — {@code souther compile
 * <file.sou> -d <outdir>} is the compiler's interface, and a reader over any wire learns the same
 * true thing from it. The other tells the reader to go and do something, and that one is only
 * followed by a reader who can. A document that writes the second kind as a shell command has
 * answered every caller as though it were at a prompt.
 *
 * <p>So the second kind is written {@code {{doc:example}}} and the spelling is chosen when the text
 * is read, from the same {@link Caller} that decides what a command's own messages offer. The
 * document says which operation; this says how to ask for it.
 *
 * <p>Only operations that every caller can carry out belong here. An affordance with no spelling on
 * some wire cannot be written as one, and a document that names such a command is describing the
 * toolchain rather than offering the reader a next step.
 */
enum Affordance {

    /** Read one specification section or one shipped topic. */
    DOC("doc", true) {
        @Override
        String cli(String argument) {
            return "souther doc " + argument;
        }

        @Override
        String mcp(String argument) {
            return "doc_read {name: \"" + argument + "\"}";
        }
    },

    /** Search the specification and every shipped topic for a term. */
    DOC_SEARCH("doc-search", true) {
        @Override
        String cli(String argument) {
            return "souther doc --search " + argument;
        }

        @Override
        String mcp(String argument) {
            return "doc_search {term: \"" + argument + "\"}";
        }
    },

    /** The standard library's published surface, whole. */
    STDLIB("stdlib", false) {
        @Override
        String cli(String argument) {
            return "souther api";
        }

        @Override
        String mcp(String argument) {
            return "stdlib_api";
        }
    },

    /** A standard library module's own source, where what a signature means is written. */
    STDLIB_SOURCE("stdlib-source", true) {
        @Override
        String cli(String argument) {
            return "souther api --source " + argument;
        }

        @Override
        String mcp(String argument) {
            return "stdlib_api_source {name: \"" + argument + "\"}";
        }
    };

    /** {@code {{name}}} or {@code {{name:argument}}}, the whole of it replaced by one spelling. */
    private static final Pattern WRITTEN = Pattern.compile("\\{\\{([a-z-]+)(?::([^}]*))?}}");

    private final String written;
    private final boolean takesArgument;

    Affordance(String written, boolean takesArgument) {
        this.written = written;
        this.takesArgument = takesArgument;
    }

    abstract String cli(String argument);

    abstract String mcp(String argument);

    /** How {@code caller} asks for this, as a code span the surrounding prose reads as one. */
    String spelled(Caller caller, String argument) {
        return "`" + switch (caller) {
            case CLI -> cli(argument);
            case MCP -> mcp(argument);
        } + "`";
    }

    /**
     * {@code text} with every affordance in it spelled the way {@code caller} asks for one.
     *
     * <p>This runs before the text is ranked, cut to a snippet or printed, so that a search answers
     * over the words this caller is going to be shown. A term that names another caller's spelling
     * finding a hit here would offer, in the snippet, the operation the document was written not to
     * offer.
     *
     * <p>An affordance nothing here declares is a typo in a document, and a document that ships
     * with one would print its own markup at a reader. It is refused where it is read rather than
     * left to be noticed in an answer.
     */
    static String materialize(String text, Caller caller) {
        if (text.indexOf('{') < 0) {
            return text;
        }
        Matcher written = WRITTEN.matcher(text);
        StringBuilder spelled = new StringBuilder();
        while (written.find()) {
            written.appendReplacement(spelled,
                    Matcher.quoteReplacement(of(written.group(1), written.group(2)).spelled(
                            caller, written.group(2))));
        }
        written.appendTail(spelled);
        return spelled.toString();
    }

    private static Affordance of(String written, String argument) {
        for (Affordance affordance : values()) {
            if (affordance.written.equals(written)) {
                if (affordance.takesArgument == (argument == null)) {
                    throw new IllegalStateException("`" + written + "` is written "
                            + (affordance.takesArgument ? "with what to ask for: `{{" + written
                                    + ":<argument>}}`" : "on its own: `{{" + written + "}}`"));
                }
                return affordance;
            }
        }
        throw new IllegalStateException("no documentation affordance `" + written + "`");
    }
}
