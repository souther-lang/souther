package souther.lsp.protocol;

/**
 * An LSP completion item: the text to insert, its {@code kind} (an LSP CompletionItemKind number,
 * which the client renders as an icon), and the {@code detail} shown beside the label.
 *
 * <p>{@code detail} is where the name comes from — the module that declares it, or the library
 * qualifier it is published under — and is null for a name that comes from nowhere else: a binding
 * in force at the cursor, or a keyword. Two candidates spelled the same are told apart by it, and a
 * list of bare names with no origins is a list an author has to already know to read.
 *
 * <p>There is no two-argument form. Whether a name has an origin is something each place that builds
 * an item has to answer, and a default would let the question go unasked.
 */
public record CompletionItem(String label, int kind, String detail) {

    // The LSP CompletionItemKind numbers this server uses.
    public static final int FUNCTION = 3;
    public static final int FIELD = 5;
    public static final int VARIABLE = 6;
    public static final int CLASS = 7;
    public static final int INTERFACE = 8;
    public static final int ENUM = 13;
    public static final int KEYWORD = 14;
}
