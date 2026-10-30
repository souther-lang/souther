package souther.compiler.coverage;

import java.util.Comparator;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * A run, read as places of the numbering it was recorded under.
 *
 * <p>What every reader of a run holds, and the only thing that answers about places. A recording is
 * numbers and a numbering says what each number addresses; the two are held against each other once
 * ({@link SiteNumbering#align}), and what comes out of that is this. So a reader asking whether a
 * run went through an arm is asking about an arm of the numbering it is reading under, and there is
 * no way to ask it about a number.
 *
 * <p><b>What the alignment established.</b> That the run was recorded under a numbering equal to
 * this one — the same places addressed by the same numbers in bodies doing the same things — and
 * that every number it holds is one that numbering handed out, for the family it is read as. A
 * recording of another module, of another build of other bodies, or of a numbering that hands its
 * numbers out in another order does not align, and is refused where it arrives rather than
 * answered.
 *
 * <p><b>And which numbering that was is carried, not left at the door.</b> An address is a place of
 * some numbering, and a reader can hold two: what a value made of one numbering's places says about
 * another's is nothing, and saying it as an ordinary "no" is the very answer this exists to stop —
 * a row reported as not having reached a place it was never asked about. Checked at the moment the
 * value was made, that is a property of one call; carried, it is a property of the value, and every
 * question put to it is answered or refused.
 *
 * <p><b>Made where the alignment is made.</b> There is no way here to put places beside a numbering
 * that did not issue them.
 */
public final class AlignedObservation {

    private final NumberingIdentity numbering;

    private final Set<ArmProbe> arms;

    private final Set<SeenConditionOutcome> outcomes;

    private final Set<SeenVisit> visits;

    private final Set<WalkProbe> walks;

    private final Set<WalkProbe> walksOn;

    private final Set<SeenComparison> compared;

    AlignedObservation(NumberingIdentity numbering, Set<ArmProbe> arms,
                       Set<SeenConditionOutcome> outcomes, Set<SeenVisit> visits) {
        this(numbering, arms, outcomes, visits, Set.of(), Set.of());
    }

    AlignedObservation(NumberingIdentity numbering, Set<ArmProbe> arms,
                       Set<SeenConditionOutcome> outcomes, Set<SeenVisit> visits,
                       Set<WalkProbe> walks, Set<WalkProbe> walksOn) {
        this(numbering, arms, outcomes, visits, walks, walksOn, Set.of());
    }

    AlignedObservation(NumberingIdentity numbering, Set<ArmProbe> arms,
                       Set<SeenConditionOutcome> outcomes, Set<SeenVisit> visits,
                       Set<WalkProbe> walks, Set<WalkProbe> walksOn,
                       Set<SeenComparison> compared) {
        if (numbering == null) {
            throw new IllegalArgumentException(
                    "a run read as places is read as places of some numbering");
        }
        this.numbering = numbering;
        this.arms = Set.copyOf(arms);
        this.outcomes = Set.copyOf(outcomes);
        this.visits = Set.copyOf(visits);
        this.walks = Set.copyOf(walks);
        this.walksOn = Set.copyOf(walksOn);
        this.compared = Set.copyOf(compared);
        this.compared.forEach(each -> requireOurs(each.at().numbering(), each));
        this.arms.forEach(each -> requireOurs(each.numbering(), each));
        this.outcomes.forEach(each -> requireOurs(each.at().numbering(), each));
        this.visits.forEach(each -> requireOurs(each.at().numbering(), each));
        this.walks.forEach(each -> requireOurs(each.numbering(), each));
    }

    /** What this run is read under, which is what a place put to it has to be a place of. */
    public NumberingIdentity numbering() {
        return numbering;
    }

    /** The arms the run was recorded at, as places of this numbering. */
    public Set<ArmProbe> arms() {
        return arms;
    }

    /** The ways its conditions came out, as places of this numbering. */
    public Set<SeenConditionOutcome> outcomes() {
        return outcomes;
    }

    /** Whether the run was recorded at {@code probe}. */
    public boolean lit(ArmProbe probe) {
        requireOurs(probe.numbering(), probe);
        return arms.contains(probe);
    }

    /** The walks the run entered, as places of this numbering. */
    public Set<WalkProbe> walks() {
        return walks;
    }

    /** Whether the run entered the walk at {@code walk}. */
    public boolean entered(WalkProbe walk) {
        requireOurs(walk.numbering(), walk);
        return walks.contains(walk);
    }

    /**
     * Whether this run went the way {@code other} did: through the same arms, with every condition
     * coming out the same, on every visit kept. Which walks either entered, and how far, is not
     * part of it: no measure but the rewrites of a walk reads that, and a row taking a list one
     * element longer goes the way a row of one element went.
     */
    public boolean wentTheWayOf(AlignedObservation other) {
        return numbering.equals(other.numbering) && arms.equals(other.arms)
                && outcomes.equals(other.outcomes) && visits.equals(other.visits);
    }

    /** Whether the run took a second element of the walk at {@code walk}. */
    public boolean wentOn(WalkProbe walk) {
        requireOurs(walk.numbering(), walk);
        return walksOn.contains(walk);
    }

    /** Whether the run had the condition at {@code at} come out {@code held}. Not the same as the
     *  condition having been reached: one that came out the other way was reached and is not
     *  this. */
    public boolean saw(ConditionOutcomeSite at, boolean held) {
        requireOurs(at.numbering(), at);
        return outcomes.contains(new SeenConditionOutcome(at, held));
    }

    /**
     * Whether the run had the condition at {@code at} come out {@code held} on its {@code nth}
     * visit, counting from none. Refused for a visit the recording does not keep
     * ({@link RecordedVisit#MOST}): that is not a visit the run did not make, and answering no
     * would say so.
     */
    public boolean sawOnVisit(ConditionOutcomeSite at, int nth, boolean held) {
        requireOurs(at.numbering(), at);
        return visits.contains(new SeenVisit(at, nth, held));
    }

    /**
     * What the sides of the comparison at {@code at} came to on each visit kept, in the order of
     * the visits — none where it is no comparison of whole numbers, or the run did not reach it.
     */
    public List<SeenComparison> comparedAt(ConditionOutcomeSite at) {
        requireOurs(at.numbering(), at);
        return compared.stream().filter(each -> each.at().equals(at))
                .sorted(Comparator.comparingInt(SeenComparison::nth)).toList();
    }

    /** Whether the run reached {@code at} at all, whichever way the condition there came out. */
    public boolean reached(ConditionOutcomeSite at) {
        return saw(at, true) || saw(at, false);
    }

    private void requireOurs(NumberingIdentity of, Object place) {
        if (!numbering.equals(of)) {
            throw new IllegalArgumentException(place + " is a place of " + of
                    + ", and this run was read under " + numbering
                    + "; what one numbering's run did at another's places is nothing, and"
                    + " answering it would say a row missed a place it was never asked about");
        }
    }

    @Override
    public boolean equals(Object other) {
        return this == other
                || (other instanceof AlignedObservation that
                        && numbering.equals(that.numbering)
                        && arms.equals(that.arms)
                        && outcomes.equals(that.outcomes)
                        && visits.equals(that.visits)
                        && walks.equals(that.walks)
                        && walksOn.equals(that.walksOn)
                        && compared.equals(that.compared));
    }

    @Override
    public int hashCode() {
        return Objects.hash(numbering, arms, outcomes, visits, walks, walksOn, compared);
    }

    @Override
    public String toString() {
        return "a run of " + numbering + " at " + arms + " and " + outcomes;
    }
}
