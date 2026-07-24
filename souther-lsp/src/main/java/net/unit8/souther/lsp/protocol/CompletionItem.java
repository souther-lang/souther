package net.unit8.souther.lsp.protocol;

/**
 * An LSP completion item: the text to insert and its {@code kind} (an LSP CompletionItemKind number,
 * which the client renders as an icon).
 */
public record CompletionItem(String label, int kind) {

    // The LSP CompletionItemKind numbers this server uses.
    public static final int FUNCTION = 3;
    public static final int FIELD = 5;
    public static final int VARIABLE = 6;
    public static final int CLASS = 7;
    public static final int INTERFACE = 8;
    public static final int KEYWORD = 14;
}
