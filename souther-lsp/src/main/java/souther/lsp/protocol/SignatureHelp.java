package souther.lsp.protocol;

import java.util.List;

/**
 * The signature of the call being written, and which of its parameters the cursor is in.
 *
 * <p>{@code parameters} are the stretches of {@code label} each parameter is written over, which is
 * what the protocol highlights — held as the text rather than as offsets, since the label is built
 * here and an offset into it would be a second thing to keep in step with it.
 *
 * <p>{@code active} names one of {@code parameters} and never a place past them. The protocol reads
 * a value outside the list as none given and marks the first, so a mark past the end does not say
 * "none of these" — it says the first, which is the one furthest from what is being written. Where
 * an author has written more arguments than the declaration takes there is nothing true to say
 * here, and what this server does is say nothing.
 */
public record SignatureHelp(String label, List<String> parameters, int active) {
}
