package souther.compiler.doc;

import java.util.List;
import java.util.Locale;
import java.util.regex.Pattern;

/**
 * The forms a documentation name takes on its way to a lookup.
 *
 * <p>A name is written in more than one case before it reaches a lookup: the specification anchors
 * a diagnostic as {@code e2010} and the compiler prints the same diagnostic as {@code E2010}, which
 * is the form a reader copies. Both name the same thing, so both have to arrive at the same key.
 *
 * <p>A name is also written in more than one place. An anchor spells the words it is made of with
 * hyphens because that is what an AsciiDoc identifier may hold, and prose spells the same rule with
 * spaces. A reader who has read the rule and goes looking for it types the words. So a search asks
 * for a name by its words, and {@code an-optional-does-not-stand-in-a-boundary} and {@code an
 * optional does not stand in a boundary} are one question.
 *
 * <p>Only the keys are folded. What a name is spelled as belongs to whoever wrote it — a section
 * keeps its anchor as the specification writes it, and a shipped topic keeps a name that is also
 * the path its text is read from, which the class path resolves by the spelling on the file.
 */
final class DocName {

    /** What separates one word of a name from the next, whatever the name is written in. */
    private static final Pattern NOT_A_WORD = Pattern.compile("[^\\p{L}\\p{N}]+");

    private DocName() {}

    /** The key {@code name} is registered and asked for under. */
    static String canonical(String name) {
        return name.toLowerCase(Locale.ROOT);
    }

    /**
     * The key a search resolves {@code name} by: its words, one space between them.
     *
     * <p>This is the wider of the two folds, so a name that reaches {@link #canonical} reaches this
     * one, and a search that resolves names answers for everything the read path answers for.
     */
    static String asWords(String name) {
        return NOT_A_WORD.matcher(canonical(name)).replaceAll(" ").strip();
    }

    /**
     * Whether {@code query} is a name at all, before asking which one it is.
     *
     * <p>A query of nothing but punctuation has no words, and folds to what a name of nothing but
     * punctuation would fold to. Neither is a name, and answering one with the other would resolve
     * {@code ---} to whatever the document happened to write as {@code ___}.
     */
    static boolean isName(String query) {
        return !asWords(query).isEmpty();
    }

    /**
     * The words {@code text} is made of, each said once, in the order it says them.
     *
     * <p>A word said twice is the same word asked for twice, and a query that asks for it twice is
     * asking for what it already asked for. Counting it again would rank a section that says that
     * one word over a section that says the rest of them.
     */
    static List<String> words(String text) {
        return NOT_A_WORD.splitAsStream(canonical(text))
                .filter(word -> !word.isEmpty())
                .distinct()
                .toList();
    }
}
