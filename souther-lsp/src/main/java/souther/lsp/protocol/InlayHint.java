package souther.lsp.protocol;

/**
 * A label the editor draws inside the line, at {@code position}, without it being in the file.
 *
 * <p>{@code tooltip} is what the label does not have room to say, shown when a reader asks for it.
 * The two are not the same text at different lengths: the label is what a reader takes in without
 * looking, and anything that has to be read is the tooltip's. Null where there is nothing more.
 *
 * <p>{@code paddingLeft} is the protocol's, and it is here because whether a hint wants a space in
 * front of it is a property of the hint: {@code : Draft} written straight after a name wants none.
 */
public record InlayHint(Position position, String label, String tooltip, boolean paddingLeft) {
}
