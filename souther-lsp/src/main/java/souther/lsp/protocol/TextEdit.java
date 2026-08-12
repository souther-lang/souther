package souther.lsp.protocol;

/**
 * One replacement: the characters to write, and where.
 *
 * <p>Both halves, because what to write is not always the same at every place a rename touches. A
 * record pattern's {@code { right }} names the field it reads and binds the value under that same
 * spelling, so renaming the binding to {@code r} has to leave the field named: what goes there is
 * {@code right = r}, not {@code r}. A rename that answered with places alone left the caller to
 * write one name over all of them, which is right everywhere else and wrong here.
 */
public record TextEdit(Range range, String newText) {}
