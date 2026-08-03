package souther.lsp.protocol;

/**
 * A line of text the editor draws above {@code range} — here, what a behavior's {@code example} rows
 * cover of it.
 *
 * <p>No command. A lens the author can click is a lens they have to decide about; this one is there
 * to be read while writing the behavior underneath it, which is the only place the numbers are worth
 * anything. What to do about them is a code action on the same declaration.
 */
public record CodeLens(Range range, String title) {
}
