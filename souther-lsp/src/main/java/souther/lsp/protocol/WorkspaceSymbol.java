package souther.lsp.protocol;

/**
 * A declaration somewhere in the workspace, as something to jump to.
 *
 * <p>A {@link DocumentSymbol} says where a declaration is inside the file being read and what it
 * contains; this says which file, and nothing about what is inside — a reader looking across a
 * workspace is choosing a declaration to open, not reading one.
 */
public record WorkspaceSymbol(String name, int kind, Location location) {
}
