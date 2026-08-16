package souther.lsp.protocol;

import souther.compiler.fmt.Skeleton;

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
 *
 * <p>{@code writes} is the declaration this item writes, for an item that writes more than its own
 * label — where the holes in it are is part of it, and how those reach a client is settled where the
 * client's capabilities are read. It is null for an item that inserts what it says.
 */
public record CompletionItem(String label, int kind, String detail, Skeleton.Built writes) {

    /**
     * An item that writes what it says.
     *
     * <p>A default here and not for {@code detail}, because the two questions are not alike. An item
     * with no origin and one whose origin was not filled in read the same to whoever is choosing
     * between two candidates spelled alike, so that has to be answered. What an item inserts has an
     * answer already — a completion with nothing else to say inserts its own label, which is what
     * the protocol does with an item carrying no insertion — so saying nothing here says that.
     */
    public CompletionItem(String label, int kind, String detail) {
        this(label, kind, detail, null);
    }

    // The LSP CompletionItemKind numbers this server uses.
    public static final int FUNCTION = 3;
    public static final int FIELD = 5;
    public static final int VARIABLE = 6;
    public static final int CLASS = 7;
    public static final int INTERFACE = 8;
    public static final int ENUM = 13;
    public static final int KEYWORD = 14;
    public static final int SNIPPET = 15;
}
