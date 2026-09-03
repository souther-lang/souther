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
 * <p>The addresses are of the numbering that did the aligning, and a reader asking about a place of
 * that same numbering is asking about the same value.
 */
public record AlignedObservation(Set<ArmProbe> arms, Set<SeenComparison> comparisons) {

    /** A run that passed nowhere, aligned with nothing to align. */
    public static final AlignedObservation NONE = new AlignedObservation(Set.of(), Set.of());

    public AlignedObservation {
        arms = arms == null ? Set.of() : Set.copyOf(arms);
        comparisons = comparisons == null ? Set.of() : Set.copyOf(comparisons);
    }

    /** Whether the run was recorded at {@code probe}. */
    public boolean lit(ArmProbe probe) {
        return arms.contains(probe);
    }

    /** Whether the run had the comparison at {@code at} come out {@code held}. Not the same as the
     *  comparison having been reached: one that came out the other way was reached and is not
     *  this. */
    public boolean saw(ComparisonEmissionSite at, boolean held) {
        return comparisons.contains(new SeenComparison(at, held));
    }

    /** Whether the run reached {@code at} at all, whichever way the comparison there came out. */
    public boolean reached(ComparisonEmissionSite at) {
        return saw(at, true) || saw(at, false);
    }
}
