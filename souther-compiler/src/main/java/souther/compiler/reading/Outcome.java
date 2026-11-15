package souther.compiler.reading;

import java.util.List;

/**
 * One way a decision can be settled, as the conditions that hold when it is.
 *
 * <p>Several conditions and not one, because a decision reached under another decision is settled
 * by both: the comparison on the total is a decision only where the member is Standard, and an
 * outcome naming the comparison alone would name a combination the body has no path to.
 */
public record Outcome(List<Decision> holds) {

    public Outcome {
        holds = List.copyOf(holds);
    }

    /** What a run that settled the decision this way would be seen to have done. */
    public List<souther.compiler.coverage.ControlClaim> claims() {
        return holds.stream().map(Decision::claims).toList();
    }

    /**
     * This, as a run is seen doing it, told what a row has to be to settle the decision this way.
     *
     * <p>Where a run is seen at an arm whichever way it came, the arm is all this says, and the ways
     * that were written down for it are what the classes of the input can place. Kept beside the
     * arm and not in place of it: the arm is what witnesses and the ways are where to look.
     *
     * <p>Told only where there is one arm to tell it of. Ways of an outcome of several forks are not
     * the ways of any one of them.
     *
     * @param ways every way the decision is settled this way, as the conjunctions they were written
     *             down as; none where they were not all written down. Never some of them: a row is
     *             looked for in the union of these and nowhere else, so a way left out is rows
     *             the search is never offered
     */
    Outcome comingOutBy(List<List<Condition>> ways) {
        long arms = holds.stream().filter(each -> each.constrains() instanceof Condition.Arm).count();
        if (ways.isEmpty() || arms != 1) {
            return this;
        }
        return new Outcome(holds.stream()
                .map(each -> each.constrains() instanceof Condition.Arm at
                        ? new Decision(at.comingOutBy(ways), each.claims()) : each)
                .toList());
    }

    @Override
    public String toString() {
        return String.join(" & ", holds.stream().map(Object::toString).toList());
    }
}
