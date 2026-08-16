package souther.compiler.claims;

import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * A body saying that one case of one input position cannot arrive.
 *
 * <p>A statement and not a finding. What the model's own rules say about the same case is read
 * elsewhere and the two are put together once ({@link Claims}); until then this is what was
 * written, in the words it was written in.
 *
 * @param at      the position the case belongs to, spelled the way a rule about it is
 * @param named   the case, by the declaration it is
 * @param reasons every reason on the paths that answer nothing, in the order they are evaluated. An
 *                arm made of a {@code match} whose arms abort for different reasons has no single
 *                reason, and taking the one written above the others would name it by where it
 *                happens to sit in the file
 * @param said    where the first of them is written, which is what a diagnostic points at
 * @param stands  what reaching the fork this arm belongs to takes
 */
public record Claim(TermPath at, TypeSymbol named, List<String> reasons, SourcePos said,
                    Standing stands) {

    /**
     * What stands between the fork an arm belongs to and the caller.
     *
     * <p>The one thing that decides what an <em>admission</em> proves. A case the rules refuse
     * cannot arrive however deep the fork is; a case they leave can arrive at the position, and
     * whether it arrives <em>here</em> is another question — one that only the first fork of a body
     * answers on its own.
     */
    public sealed interface Standing {

        /** Nothing: the fork is what the body does first, so reaching it is being applied at all. */
        record Reached() implements Standing {}

        /** Another arm, whose own condition this reading does not decide. */
        record Conditional() implements Standing {}
    }

    public Claim {
        reasons = List.copyOf(reasons);
    }
}
