package souther.compiler.claims;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.UnreachableMessage;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * What is said about a claim the model's own rules contradict.
 *
 * <p>One arm of {@link ClaimVerdict} reaches here and the other two do not. A claim the rules bear
 * out is what the report prints, and one nothing settled is what it says was not settled; only a
 * claim the rules refute is a model saying two things at once, and that is a compile error rather
 * than a line in a report — a report of a model can be read or not, and this is a premise the model
 * would abort on.
 *
 * <p>Three values, because all three are what an author needs to act: where the claim is written,
 * which case it is about and which position that case can arrive at, and which declaration says it
 * can. The last is what makes the answer actionable — the arm answers a value, or that declaration
 * changes.
 */
public final class ClaimDiagnostics {

    /** Every claim the rules contradict, in the order the body makes them. */
    public static List<Diagnostic> refusals(Claims judged, InputDomain read) {
        List<Diagnostic> out = new ArrayList<>();
        for (Claims.Judged each : judged.thatAre(ClaimVerdict.Contradicted.class)) {
            Diagnostic said = refusal(each.claim(), read.at(each.claim().at()));
            if (said != null) {
                out.add(said);
            }
        }
        return List.copyOf(out);
    }

    /**
     * One refusal, or nothing where there is nowhere to point.
     *
     * <p>An arm answering nothing with no {@code unreachable} in it has no place of its own — a
     * construction one of whose fields aborts is one, and what aborts there is reported where it is
     * written. Nothing is said rather than said at the behavior: a diagnostic whose place is not the
     * thing it is about sends a reader somewhere they cannot act.
     */
    private static Diagnostic refusal(Claim claim, Position at) {
        if (claim.said() == null || at == null) {
            return null;
        }
        return Diagnostic.at(claim.said())
                .say(new UnreachableMessage.TheModelAdmitsThisCase(claim.named().name(),
                        claim.at().toString()))
                .hint(new UnreachableMessage.ItIsACaseOf(claim.named().name(),
                        Type.show(at.type())))
                .hint(new UnreachableMessage.AnswerAValueOrChangeTheInput())
                .build();
    }

    private ClaimDiagnostics() {}
}
