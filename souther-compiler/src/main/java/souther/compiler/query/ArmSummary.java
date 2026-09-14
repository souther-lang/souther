package souther.compiler.query;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

/**
 * What a behavior's arms came to, in the groups a surface counts and names them in.
 *
 * <p>The one thing a consumer of the arm measure reads. A report's line, the marks under it, the
 * findings a build refuses over, the document's entries and an editor's summary are all projections
 * of this, and every one of them used to be worked out from a different pair of accessors —
 * a count here, a claim there, and a word for how far the measurement got, which each of them read
 * its own condition off.
 *
 * <p><b>Everything the numbers hold is in {@link #all}, once.</b> The denominator is
 * {@link #counted()} and every arm in it is in exactly one of {@link #met()}, {@link #unmet()} and
 * {@link #undecided()}, so a surface that prints the two numbers and then walks the last two has
 * said what the difference between them is. What is outside the count is {@link #notCounted()} and
 * says why.
 *
 * <p><b>And the count itself is qualified.</b> {@link #census()} says whether the set of arms the
 * numbers are over is the set the behavior owes. It travels with the groups because it is about
 * them: handed the groups alone, a surface wanting the qualification would have to go back to what
 * weakened the measurement and work out from the reasons there which of them was about the
 * denominator — which is reading an account out of its provenance, the thing this normal form exists
 * to stop.
 */
public record ArmSummary(List<ArmObligation> all, ArmCensus census) {

    public ArmSummary {
        all = List.copyOf(all);
        java.util.Objects.requireNonNull(census, "an account says whether its denominator stands");
    }

    /** The arms a row goes through. */
    public List<ArmObligation.Counted> met() {
        return counted(ArmDisposition.MET);
    }

    /** The arms no row goes through, where every row was read. One finding each. */
    public List<ArmObligation.Counted> unmet() {
        return counted(ArmDisposition.UNMET);
    }

    /** The arms nobody could decide. Named, and never a finding. */
    public List<ArmObligation.Counted> undecided() {
        return counted(ArmDisposition.UNDECIDED);
    }

    /** The arms outside the count, each with why it is out. */
    public List<ArmObligation.NotCounted> notCounted() {
        List<ArmObligation.NotCounted> out = new ArrayList<>();
        for (ArmObligation each : all) {
            if (each instanceof ArmObligation.NotCounted it) {
                out.add(it);
            }
        }
        return List.copyOf(out);
    }

    /**
     * The reasons arms are outside the count, one per fork rather than one per arm.
     *
     * <p>Both arms of one fork are out together or neither is, so a reader is told once what is
     * uncertain about it. Grouped here and not by whoever is writing a sentence: two surfaces
     * grouping the same list are two answers to how many facts there are.
     */
    public List<ArmExclusion> exclusions() {
        return List.copyOf(new LinkedHashSet<>(notCounted().stream()
                .map(ArmObligation.NotCounted::because).toList()));
    }

    /** How many arms the count holds, which is the denominator a surface prints. */
    public int counted() {
        return met().size() + unmet().size() + undecided().size();
    }

    /** How many of them a row goes through, which is the numerator. */
    public int covered() {
        return met().size();
    }

    private List<ArmObligation.Counted> counted(ArmDisposition where) {
        List<ArmObligation.Counted> out = new ArrayList<>();
        for (ArmObligation each : all) {
            if (each instanceof ArmObligation.Counted it && it.disposition() == where) {
                out.add(it);
            }
        }
        return List.copyOf(out);
    }
}
