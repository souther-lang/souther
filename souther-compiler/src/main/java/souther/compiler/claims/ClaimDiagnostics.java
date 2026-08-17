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
     * One refusal, or nothing where there is no position to have refused it.
     *
     * <p>A claim always has somewhere to point — an arm answers nothing by reaching an
     * {@code unreachable}, which is where it is written. What can be absent is the position: a claim
     * about one this reading never made is unproven and never arrives here.
     */
    private static Diagnostic refusal(Claim claim, Position at) {
        if (at == null) {
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
