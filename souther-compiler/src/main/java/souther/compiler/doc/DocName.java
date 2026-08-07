package souther.compiler.doc;

import java.util.Locale;

/**
 * The one form a documentation name is looked up by.
 *
 * <p>A name is written in more than one case before it reaches a lookup: the specification anchors
 * a diagnostic as {@code e2010} and the compiler prints the same diagnostic as {@code E2010}, which
 * is the form a reader copies. Both name the same thing, so both have to arrive at the same key.
 *
 * <p>Only the key is folded. What a name is spelled as belongs to whoever wrote it — a section
 * keeps its anchor as the specification writes it, and a shipped topic keeps a name that is also
 * the path its text is read from, which the class path resolves by the spelling on the file.
 */
final class DocName {

    private DocName() {}

    /** The key {@code name} is registered and asked for under. */
    static String canonical(String name) {
        return name.toLowerCase(Locale.ROOT);
    }
}
