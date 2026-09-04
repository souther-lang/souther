package souther.compiler.coverage;

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

    private final Set<SeenComparison> comparisons;

    AlignedObservation(NumberingIdentity numbering, Set<ArmProbe> arms,
                       Set<SeenComparison> comparisons) {
        if (numbering == null) {
            throw new IllegalArgumentException(
                    "a run read as places is read as places of some numbering");
        }
        this.numbering = numbering;
        this.arms = Set.copyOf(arms);
        this.comparisons = Set.copyOf(comparisons);
        this.arms.forEach(each -> requireOurs(each.numbering(), each));
        this.comparisons.forEach(each -> requireOurs(each.at().numbering(), each));
    }

    /** What this run is read under, which is what a place put to it has to be a place of. */
    public NumberingIdentity numbering() {
        return numbering;
    }

    /** The arms the run was recorded at, as places of this numbering. */
    public Set<ArmProbe> arms() {
        return arms;
    }

    /** The ways its comparisons came out, as places of this numbering. */
    public Set<SeenComparison> comparisons() {
        return comparisons;
    }

    /** Whether the run was recorded at {@code probe}. */
    public boolean lit(ArmProbe probe) {
        requireOurs(probe.numbering(), probe);
        return arms.contains(probe);
    }

    /** Whether the run had the comparison at {@code at} come out {@code held}. Not the same as the
     *  comparison having been reached: one that came out the other way was reached and is not
     *  this. */
    public boolean saw(ComparisonEmissionSite at, boolean held) {
        requireOurs(at.numbering(), at);
        return comparisons.contains(new SeenComparison(at, held));
    }

    /** Whether the run reached {@code at} at all, whichever way the comparison there came out. */
    public boolean reached(ComparisonEmissionSite at) {
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
                        && comparisons.equals(that.comparisons));
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(numbering, arms, comparisons);
    }

    @Override
    public String toString() {
        return "a run of " + numbering + " at " + arms + " and " + comparisons;
    }
}
