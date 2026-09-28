package souther.compiler.cst;

/**
 * A word the grammar reads as a keyword in some places and leaves a name everywhere else.
 *
 * <p>None of these is reserved: {@code example.*} is a module namespace, and a field or a parameter
 * may be named {@code on}. The lexer hands every one of them over as an {@link SyntaxKind#IDENT},
 * and where the parser reads one as a keyword it writes it into the tree as a {@link
 * SyntaxKind#CONTEXTUAL_KW}. A reader of the tree then asks the tree what a word was read as, and
 * never works it out again from where the word stands.
 *
 * <p>This is the vocabulary and nothing more. Where each word is a keyword is the parser's, where
 * the grammar is; which of them open a top-level form is {@link TopLevelForm}'s.
 */
public enum ContextualWord {

    EXAMPLES("examples"),
    FOR("for"),
    EXAMPLE("example"),
    FAKE("fake"),
    PRIVATE("private"),
    PARTIAL("partial"),
    ON("on"),
    INTRINSIC("intrinsic");

    private final String spelling;

    ContextualWord(String spelling) {
        this.spelling = spelling;
    }

    public String spelling() {
        return spelling;
    }
}
