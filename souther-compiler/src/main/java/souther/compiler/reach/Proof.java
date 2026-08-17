package souther.compiler.reach;

import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * How it was shown that nothing arrives.
 *
 * <p>Cut by what was shown and not by what showed it — the same rule the emptiness proofs are under.
 * A domain added to the reading writes one of these, and only a new thing to <em>say</em> earns a
 * new arm. Named after the domain that found it, every domain would be an arm, and the sentence an
 * author reads would change when an implementation did.
 *
 * <p>Read by the renderer that writes the sentence and by nothing else. Whoever decides an
 * obligation or a claim reads {@link Reachability} and treats this as payload, so an arm added here
 * is a compile error in one place and a change to no policy.
 */
public sealed interface Proof {

    /**
     * The conditions on the way here cannot all hold.
     *
     * <p>The general form: what is known is that together they leave nothing, and which of them is
     * doing it is not claimed. A smallest set that still contradicts would be a nicer sentence and
     * is a different piece of work — one this does not pretend to have done.
     *
     * @param decisions the conditions taken in on the way here, in the order they were assumed
     */
    record ConflictingPathConditions(List<PathDecision> decisions) implements Proof {

        public ConflictingPathConditions {
            decisions = List.copyOf(decisions);
            if (decisions.isEmpty()) {
                throw new IllegalArgumentException(
                        "conditions that cannot all hold, with no condition among them");
            }
        }
    }

    /**
     * The values the comparison here admits are not values the position can hold.
     *
     * <p>Nearer than the general form, and about the declaration rather than about the path: what
     * the rules leave a position is what a comparison is held against, and a comparison outside it
     * divides nothing and is taken by nothing.
     *
     * @param position how the position is spelled where a rule about it is written
     * @param admits   what the rules leave it, as a report may say it
     */
    record OutsideWhatThePositionHolds(String position, String admits) implements Proof {}

    /**
     * Every case this arm is written for is one the rules refuse at the position matched on.
     *
     * <p>Unconditional, so it holds as truly under three enclosing arms as at the first fork: a
     * refusal is about the position and not about the way here.
     */
    record EveryCaseRefused(String position, List<TypeSymbol> cases) implements Proof {

        public EveryCaseRefused {
            cases = List.copyOf(cases);
            if (cases.isEmpty()) {
                throw new IllegalArgumentException("every case refused, of no cases");
            }
        }
    }
}
