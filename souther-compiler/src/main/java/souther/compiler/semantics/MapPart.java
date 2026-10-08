package souther.compiler.semantics;

/**
 * What of a map a list of it holds.
 *
 * <p>A word about what an operation answers, beside the fact that says so and not inside it: a
 * reader of the fact once it is bound reads which part the list holds, and has no use for how the
 * fact was authored.
 */
public enum MapPart {
    /** The keys, one per entry. */
    KEYS,
    /** The values, one per entry. */
    VALUES,
    /** The entries, each a pair of its key and its value, in that order. */
    ENTRIES
}
