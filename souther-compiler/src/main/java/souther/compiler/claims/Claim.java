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
 */
public record Claim(TermPath at, TypeSymbol named, List<String> reasons, SourcePos said) {

    public Claim {
        reasons = List.copyOf(reasons);
    }
}
