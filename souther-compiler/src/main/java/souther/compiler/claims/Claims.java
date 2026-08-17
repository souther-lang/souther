package souther.compiler.claims;

import souther.compiler.inputs.Admits;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Unsettlement;

import java.util.ArrayList;
import java.util.List;

/**
 * A behavior's claims, held against the reading of its input.
 *
 * <p>The one place the two meet. Whether a case declared unreachable is refused, left owed with the
 * claim named as unproven, or reported as a contradiction is one decision, and a decision made per
 * measure is one each measure can make differently — which is how a case left the signature's
 * denominator while the rules that would have refuted it were never asked.
 *
 * <p>What comes out of here reaches a diagnostic and a report and nothing else. The denominators are
 * the reading's, before this runs and after it.
 */
public final class Claims {

    /** Nothing claimed, which is what a behavior with no body and most bodies come to. */
    public static final Claims NONE = new Claims(List.of());

    /** One claim and what the rules said about it. */
    public record Judged(Claim claim, ClaimVerdict verdict) {}

    private final List<Judged> judged;

    private Claims(List<Judged> judged) {
        this.judged = List.copyOf(judged);
    }

    /**
     * Every claim {@code claims} makes, judged against {@code read}.
     *
     * <p>A claim naming a position the reading has none of is unproven rather than anything else:
     * what would settle it was never read, and a target nothing resolves is a fact about how far
     * this compiler walks rather than about the model.
     */
    public static Claims of(UnreachableClaims claims, InputDomain read) {
        if (claims.isEmpty()) {
            return NONE;
        }
        List<Judged> out = new ArrayList<>();
        for (Claim claim : claims.all()) {
            out.add(new Judged(claim, verdictOf(claim, read.at(claim.at()))));
        }
        return new Claims(out);
    }

    /** What the rules say about one claim. */
    private static ClaimVerdict verdictOf(Claim claim, Position at) {
        if (at == null) {
            return new ClaimVerdict.Unproven(new Unsettlement.NoSuchDistinction());
        }
        return switch (at.admissionOf(claim.named())) {
            case Admits.Refused _ -> new ClaimVerdict.Confirmed();
            // What an admission comes to turns on what stands above the arm. A case the rules leave
            // arrives at the position; whether it arrives at a fork inside another arm is a
            // question about that arm's own condition, and nothing here reads one.
            case Admits.Admitted _ -> claim.stands() instanceof Claim.Standing.Reached
                    ? new ClaimVerdict.Contradicted()
                    : new ClaimVerdict.Unproven(new Unsettlement.ForkNotKnownToBeReached());
            case Admits.Unsettled unsettled -> new ClaimVerdict.Unproven(unsettled.why());
        };
    }

    public boolean isEmpty() {
        return judged.isEmpty();
    }

    /** Every claim with what was said about it, in the order the body makes them. */
    public List<Judged> all() {
        return judged;
    }

    /** The claims of one kind, which is how a diagnostic asks for the ones it refuses and a report
     *  for the ones it prints. */
    public List<Judged> thatAre(Class<? extends ClaimVerdict> verdict) {
        return judged.stream().filter(each -> verdict.isInstance(each.verdict())).toList();
    }
}
