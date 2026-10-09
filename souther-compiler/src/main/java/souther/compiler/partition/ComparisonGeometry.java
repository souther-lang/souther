package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

/**
 * What one read comparison adds to the partition's geometry: the evidence a value at or dividing
 * a position states, and the lines drawn between positions a comparison relates but does not
 * divide.
 *
 * <p>{@link GuardThresholds} and {@link EnsuresThresholds} each read this off {@link
 * ComparisonAssessment} the same way — only the two arms that draw something have anything to
 * add, and what each of those adds is settled by {@link ComparisonAssessment.AtAPosition#cutting}
 * or {@link ComparisonAssessment.AcrossPositions#cutting} alone — and a statement of several adds
 * what each of its lines adds. What the two readers do not
 * share is where a line's origin comes from — a guard's from the comparison's own place in the
 * body, a clause's from which conjunct stated it — which is the one thing {@code originOf} still
 * supplies. What each place this comparison names is left with, where no line was drawn, is
 * {@link ComparisonAssessment#whatEachPlaceIsLeftWith}'s answer and is not read again here.
 */
record ComparisonGeometry(List<LineEvidence> evidence, List<LineDrawn> between) {

    private static final ComparisonGeometry NONE = new ComparisonGeometry(List.of(), List.of());

    ComparisonGeometry {
        evidence = List.copyOf(evidence);
        between = List.copyOf(between);
    }

    /**
     * Where a line comes from, which is the one thing about it the reader that met it says.
     *
     * <p>Asked with which of a statement's lines it is, where the comparison states several: the
     * line is one rule's, and which of its lines is part of saying which line it is.
     */
    @FunctionalInterface
    interface OriginOf {

        /**
         * The origin of the line drawn on {@code cutting}.
         *
         * @param part which of the comparison's lines this is and the case of where it decides it
         *             is read in, or empty where the comparison states one
         */
        LineOrigin of(Cutting cutting, Optional<WhereAPartDecides> part);
    }

    /**
     * The geometry {@code assessed} adds, with {@code originOf} answering where a line drawn on
     * one cutting comes from.
     */
    static ComparisonGeometry of(ComparisonAssessment assessed, OriginOf originOf) {
        if (!(assessed instanceof ComparisonAssessment.Several several)) {
            return ofALine(assessed, cutting -> originOf.of(cutting, Optional.empty()));
        }
        // What each of its lines adds, once for each case where it decides — each a reading of the
        // line, whose origin says which line it is and which case it is read in.
        List<LineEvidence> evidence = new ArrayList<>();
        List<LineDrawn> between = new ArrayList<>();
        for (ComparisonAssessment.Several.Part part : several.parts()) {
            for (WhereAPartDecides reading : part.readings()) {
                ComparisonGeometry line = ofALine(part.line(),
                        cutting -> originOf.of(cutting, Optional.of(reading)));
                evidence.addAll(line.evidence());
                between.addAll(line.between());
            }
        }
        return new ComparisonGeometry(evidence, between);
    }

    /** What one line adds, its origin answered by {@code originOf}. */
    private static ComparisonGeometry ofALine(ComparisonAssessment assessed,
                                              Function<Cutting, LineOrigin> originOf) {
        return switch (assessed) {
            case ComparisonAssessment.AtAPosition at -> atAPosition(at, originOf.apply(at.cutting()));
            // A value singled out on such a quantity has no sides, so there is nothing for a
            // border to owe a row away from.
            case ComparisonAssessment.AcrossPositions over -> over.drawsABorder()
                    ? new ComparisonGeometry(List.of(),
                            List.of(new LineDrawn(over.cutting(), originOf.apply(over.cutting()))))
                    : NONE;
            case ComparisonAssessment.Several _ -> throw new IllegalArgumentException(
                    "a line of a statement is one line: " + assessed);
            case ComparisonAssessment.AnswerDependent _,
                 ComparisonAssessment.OnADependencysAnswer _, ComparisonAssessment.NoInput _,
                 ComparisonAssessment.CutsNothing _, ComparisonAssessment.OutsideTheDomain _,
                 ComparisonAssessment.NothingArrivesAtItsLine _,
                 ComparisonAssessment.TurnsNothing _,
                 ComparisonAssessment.NoFeasibleInput _, ComparisonAssessment.Unread _ -> NONE;
        };
    }

    private static ComparisonGeometry atAPosition(ComparisonAssessment.AtAPosition at,
                                                   LineOrigin origin) {
        List<LineEvidence> evidence = new ArrayList<>();
        // The value the rule names, which is where its line falls and not the value beside it. A
        // rule that names no value of the position singles nothing out here — the position is
        // divided all the same, and what divides it is the line.
        switch (at.cutting().claim()) {
            case ComparisonClaim.Singled _ -> {
                if (at.value() != null) {
                    evidence.add(new LineEvidence(new RuleEvidence.Singles(
                            new GuardThresholds.Guards.Singled(at.position(), at.value(), origin)),
                            at.cutting()));
                }
            }
            // The seam is one the assessment asked for and held: a line whose sides were not worked
            // out is assessed as unread and never reaches here as a line on a position.
            case ComparisonClaim.Cut order -> evidence.add(new LineEvidence(new RuleEvidence.Divides(
                    new Threshold(at.position(),
                            at.cutting().seam().orFail("a line on a position was assessed"
                                    + " with the values beside it not worked out"),
                            order.valueBelongs(), origin)), at.cutting()));
        }
        // And the line itself, where the position has no value beside it for a row to be owed at.
        List<LineDrawn> between = at.value() == null && at.drawsABorder()
                ? List.of(new LineDrawn(at.cutting(), origin))
                : List.of();
        return new ComparisonGeometry(evidence, between);
    }
}
