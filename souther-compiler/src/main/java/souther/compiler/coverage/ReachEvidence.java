package souther.compiler.coverage;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Stream;

/**
 * What the runs of a module did that can show a proof about reach wrong.
 *
 * <p>The arms they went through, the ways their conditions came out, and the walks they took a
 * second element of: one value, because a proof is taken back by whatever a run did, and a reading
 * handed the kinds one at a time can be handed fewer of them without anything saying so. An empty
 * kind is then both "no run did that" and "nobody passed it". Made from the runs, every kind is
 * gathered in the one place that reads a run, and a kind added to what a run shows wrong is added
 * to this and to nothing at the places that hand runs over.
 *
 * <p>Made only from runs ({@link #ofRuns}), and from no places written down: a run that did only
 * some of these is a run, and evidence short of a kind is not something that can be made.
 *
 * <p>Runs are not kept apart: a place is shown wrong by any run at it, and which run it was is no
 * part of that.
 */
public final class ReachEvidence {

    /** Evidence of no run: nothing went anywhere, and no proof is gone against. */
    public static final ReachEvidence NONE = new ReachEvidence(Set.of(), Set.of(), Set.of());

    private final Set<ArmProbe> arms;

    private final Set<SeenConditionOutcome> outcomes;

    private final Set<WalkProbe> walksOn;

    private ReachEvidence(Set<ArmProbe> arms, Set<SeenConditionOutcome> outcomes,
                          Set<WalkProbe> walksOn) {
        this.arms = Set.copyOf(arms);
        this.outcomes = Set.copyOf(outcomes);
        this.walksOn = Set.copyOf(walksOn);
    }

    /** What {@code runs} did, between them. Read once, which is what a stream is for. */
    public static ReachEvidence ofRuns(Stream<AlignedObservation> runs) {
        Set<ArmProbe> arms = new LinkedHashSet<>();
        Set<SeenConditionOutcome> outcomes = new LinkedHashSet<>();
        Set<WalkProbe> walksOn = new LinkedHashSet<>();
        for (Iterator<AlignedObservation> each = runs.iterator(); each.hasNext();) {
            AlignedObservation run = each.next();
            arms.addAll(run.arms());
            outcomes.addAll(run.outcomes());
            run.walks().stream().filter(run::wentOn).forEach(walksOn::add);
        }
        return new ReachEvidence(arms, outcomes, walksOn);
    }

    /** The arms some run went through. */
    public Set<ArmProbe> arms() {
        return arms;
    }

    /** The ways some run saw a condition come out. */
    public Set<SeenConditionOutcome> outcomes() {
        return outcomes;
    }

    /** The walks some run took a second element of. */
    public Set<WalkProbe> walksOn() {
        return walksOn;
    }

    @Override
    public boolean equals(Object other) {
        return this == other
                || (other instanceof ReachEvidence that && arms.equals(that.arms)
                        && outcomes.equals(that.outcomes) && walksOn.equals(that.walksOn));
    }

    @Override
    public int hashCode() {
        return Objects.hash(arms, outcomes, walksOn);
    }

    @Override
    public String toString() {
        return "evidence of arms " + arms + ", outcomes " + outcomes + " and walks " + walksOn;
    }
}
