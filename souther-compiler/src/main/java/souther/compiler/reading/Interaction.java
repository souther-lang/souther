package souther.compiler.reading;

import java.util.List;

/**
 * The decisions that determine one value together, and what a row has to do to get to them.
 *
 * <p>What a black-box combination measure has to assume about every pair of inputs, read instead. A
 * group is where two values each settled by a decision are consumed into one, so the answer is a
 * function of both and a row that leaves either of them at one outcome cannot tell what was done
 * with them.
 *
 * <p>Two halves and both are needed. An operator standing in an arm is reached only by a row that
 * takes that arm, and a row that varies the factors while going the other way exercises the
 * operator not at all — so a group is a path to the meeting as much as it is the outcomes at it.
 * Left out, a row offered for one of these combinations may never reach the operator, and a row
 * already written on the other side of the fork reads as one that covers it.
 *
 * <p>A meeting where no way in can be stated, under a step nothing of the input states, is still a
 * meeting and still asked for: its combinations are what its decisions are, and a run is seen
 * making one by what it does at them. What is not stated is how a row gets there, so nothing of the
 * way in holds a combination and nothing says where a row is looked for.
 *
 * @param reach       what holds on the way to the meeting, which every one of its combinations is
 *                    under; none where that is not stated
 * @param reachStated whether {@code reach} is the way in to the meeting. Where it is not, the
 *                    meeting is reached some way that is not known, and {@code reach} is empty
 * @param factors     what varies at it, one per value consumed there
 */
public record Interaction(List<Decision> reach, boolean reachStated, List<Factor> factors) {

    public Interaction {
        reach = List.copyOf(reach);
        factors = List.copyOf(factors);
        if (!reachStated && !reach.isEmpty()) {
            throw new IllegalArgumentException("a way in that is not stated holds nothing: " + reach);
        }
    }

    /** A meeting reached some way that cannot be stated. */
    public static Interaction reachedSomeWay(List<Factor> factors) {
        return new Interaction(List.of(), false, factors);
    }

    /** What a run that took the way to the meeting would be seen to have done. */
    public List<souther.compiler.coverage.ControlClaim> reachClaims() {
        return reach.stream().map(Decision::claims).toList();
    }

    @Override
    public String toString() {
        return reach.isEmpty() ? factors.toString() : reach + " => " + factors;
    }
}
