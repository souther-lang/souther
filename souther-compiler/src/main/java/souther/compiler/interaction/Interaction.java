package souther.compiler.interaction;

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
 * @param reach   what holds on the way to the meeting, which every one of its combinations is under
 * @param factors what varies at it, one per value consumed there
 */
public record Interaction(List<Condition> reach, List<Factor> factors) {

    public Interaction {
        reach = List.copyOf(reach);
        factors = List.copyOf(factors);
    }

    @Override
    public String toString() {
        return reach.isEmpty() ? factors.toString() : reach + " => " + factors;
    }
}
