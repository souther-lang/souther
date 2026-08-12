package souther.compiler.editor;

/**
 * What an editor makes of a symbol the language writes.
 *
 * <p>This is a presentation question and not a syntactic one. The specification's inventory divides
 * the same symbols into operators and delimiters by what they do — {@code ->} joins two types and
 * computes nothing, so it is a delimiter there — and an editor is asking something else: which
 * symbols a reader wants told apart from the names and the brackets around them.
 */
public enum EditorSymbolClass {

    /** Painted as an operator: given a colour of its own. */
    OPERATOR,

    /** Left in the colour of the text: the brackets, the separators and the dot. */
    PUNCTUATION
}
