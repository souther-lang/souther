package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

/**
 * What one read comparison adds to the partition's geometry: the evidence a value at or dividing
 * a position states, and the lines drawn between positions a comparison relates but does not
 * divide.
 *
 * <p>{@link GuardThresholds} and {@link EnsuresThresholds} each read this off {@link
 * ComparisonAssessment} the same way — only the two arms that draw something have anything to
 * add, and what each of those adds is settled by {@link ComparisonAssessment.AtAPosition#cutting}
 * or {@link ComparisonAssessment.AcrossPositions#cutting} alone. What the two readers do not
 * share is where a line's origin comes from — a guard's from the comparison's own place in the
 * body, a clause's from which conjunct stated it — which is the one thing {@code originOf} still
 * supplies. What each place this comparison names is left with, where no line was drawn, is
 * {@link ComparisonAssessment#whatEachPlaceIsLeftWith}'s answer and is not read again here.
 */
record ComparisonGeometry(List<RuleEvidence> evidence, List<LineDrawn> between) {

    private static final ComparisonGeometry NONE = new ComparisonGeometry(List.of(), List.of());

    ComparisonGeometry {
        evidence = List.copyOf(evidence);
        between = List.copyOf(between);
    }

    /**
     * The geometry {@code assessed} adds, with {@code originOf} answering where a line drawn on
     * one cutting comes from.
     */
    static ComparisonGeometry of(ComparisonAssessment assessed,
                                 Function<Cutting, ? extends LineOrigin> originOf) {
        return switch (assessed) {
            case ComparisonAssessment.AtAPosition at -> atAPosition(at, originOf.apply(at.cutting()));
            // A value singled out on such a quantity has no sides, so there is nothing for a
            // border to owe a row away from.
            case ComparisonAssessment.AcrossPositions over -> over.drawsABorder()
                    ? new ComparisonGeometry(List.of(),
                            List.of(new LineDrawn(over.cutting(), originOf.apply(over.cutting()))))
                    : NONE;
            case ComparisonAssessment.AnswerDependent _, ComparisonAssessment.NoInput _,
                 ComparisonAssessment.CutsNothing _, ComparisonAssessment.OutsideTheDomain _,
                 ComparisonAssessment.NothingArrivesAtItsLine _,
                 ComparisonAssessment.NoFeasibleInput _, ComparisonAssessment.Unread _ -> NONE;
        };
    }

    private static ComparisonGeometry atAPosition(ComparisonAssessment.AtAPosition at,
                                                   LineOrigin origin) {
        List<RuleEvidence> evidence = new ArrayList<>();
        // The value the rule names, which is where its line falls and not the value beside it. A
        // rule that names no value of the position singles nothing out here — the position is
        // divided all the same, and what divides it is the line.
        switch (at.cutting().claim()) {
            case ComparisonClaim.Singled _ -> {
                if (at.value() != null) {
                    evidence.add(new RuleEvidence.Singles(
                            new GuardThresholds.Guards.Singled(at.position(), at.value(), origin)));
                }
            }
            case ComparisonClaim.Cut order -> evidence.add(new RuleEvidence.Divides(
                    new Threshold(at.position(), at.cutting().seam(), order.valueBelongs(), origin)));
        }
        // And the line itself, where the position has no value beside it for a row to be owed at.
        List<LineDrawn> between = at.value() == null && at.drawsABorder()
                ? List.of(new LineDrawn(at.cutting(), origin))
                : List.of();
        return new ComparisonGeometry(evidence, between);
    }
}
