package souther.compiler.coverage;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * A run made up to be exactly what some claims name.
 *
 * <p>What a fixture reaches for when the question is what a reader does with a run, rather than what
 * running produces. The places come off the claims, so a fixture cannot write a run at a place no
 * claim is about — which is the mistake that makes such a test pass for a reason nobody chose.
 *
 * <p>Already aligned, because there is nothing to align: the claims carry addresses of a numbering,
 * and a run built out of them is of that numbering by construction. A fixture that wants the
 * crossing itself tested writes an {@link Observation} and calls {@link SiteNumbering#align}.
 */
public final class Runs {

    /** A run that did everything {@code claims} names and nothing else. */
    public static AlignedObservation doing(List<ControlClaim> claims) {
        Set<ArmProbe> arms = new LinkedHashSet<>();
        Set<SeenComparison> ways = new LinkedHashSet<>();
        for (ControlClaim claim : claims) {
            switch (claim.at()) {
                case ControlPointId.ArmOccurrence arm -> arm.probe().ifPresent(arms::add);
                case ControlPointId.ComparisonPoint point ->
                        ways.add(new SeenComparison(point.at(), point.held()));
            }
        }
        return new AlignedObservation(arms, ways);
    }

    private Runs() {}
}
