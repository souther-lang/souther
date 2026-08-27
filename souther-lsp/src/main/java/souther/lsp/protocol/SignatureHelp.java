package souther.lsp.protocol;

import java.util.List;
import java.util.OptionalInt;

/**
 * The signature of the call being written, and which of its parameters the cursor is in.
 *
 * <p>{@code parameters} are the stretches of {@code label} each parameter is written over, which is
 * what the protocol highlights — held as the text rather than as offsets, since the label is built
 * here and an offset into it would be a second thing to keep in step with it.
 *
 * <p>A signature that takes nothing has nothing to mark, and a signature that takes something marks
 * one of the things it takes. The two go together, so they are one thing to get right: the
 * constructor refuses an active parameter where there are none, refuses none where there are, and
 * refuses one that names a parameter that was not sent. What the protocol does with a mark outside
 * the list is read it as none given and mark the first — so a value past the end does not say "none
 * of these", it says the one furthest from what is being written.
 */
public record SignatureHelp(String label, List<String> parameters, OptionalInt active) {

    public SignatureHelp {
        parameters = List.copyOf(parameters);
        if (parameters.isEmpty() != active.isEmpty()) {
            throw new IllegalArgumentException(parameters.isEmpty()
                    ? "a signature that takes nothing marks nothing: " + label
                    : "a signature that takes something marks one of them: " + label);
        }
        if (active.isPresent() && (active.getAsInt() < 0
                || active.getAsInt() >= parameters.size())) {
            throw new IllegalArgumentException(
                    "a mark on a parameter that was not sent: " + active + " of " + parameters);
        }
    }
}
