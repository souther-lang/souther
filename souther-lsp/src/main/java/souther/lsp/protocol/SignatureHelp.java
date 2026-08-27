package souther.lsp.protocol;

import java.util.List;

/**
 * The signature of the call being written, and which of its parameters the cursor is in.
 *
 * <p>{@code parameters} are the stretches of {@code label} each parameter is written over, which is
 * what the protocol highlights — held as the text rather than as offsets, since the label is built
 * here and an offset into it would be a second thing to keep in step with it.
 *
 * <p>{@code active} may point past the end. An author writing a fourth argument to a behavior that
 * takes three is writing something the model refuses, and moving the mark back to the last parameter
 * would say they are still writing that one.
 */
public record SignatureHelp(String label, List<String> parameters, int active) {
}
