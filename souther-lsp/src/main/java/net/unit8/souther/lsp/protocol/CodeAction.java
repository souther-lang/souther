package net.unit8.souther.lsp.protocol;

/**
 * A quick-fix code action: its {@code title}, and the single edit it applies — replacing
 * {@code range} in the document {@code uri} with {@code newText}.
 */
public record CodeAction(String title, String uri, Range range, String newText) {
}
