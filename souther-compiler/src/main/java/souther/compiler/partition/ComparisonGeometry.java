package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.meaning.AuthoredPointMapping;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.BiFunction;

/**
 * What one read comparison adds to the partition's geometry: the evidence a value at or dividing
 * a position states, and the lines drawn between positions a comparison relates but does not
 * divide.
 *
 * <p>{@link GuardThresholds} and {@link EnsuresThresholds} each read this off {@link
 * ComparisonAssessment} the same way — only the arms that draw something have anything to add,
 * and what each of those adds is settled by {@link ComparisonAssessment.AtAPosition#cutting},
 * {@link ComparisonAssessment.AcrossPositions#cutting} and the lines parting the values that
 * settle a relation alone — and a statement of several adds what each of its lines adds. What the
 * two readers do not
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
         * @param part     which of the comparison's lines this is and the case of where it decides
         *                 it is read in, or empty where the comparison states one
         * @param authored how the line stands to the line of its author's it is a place of
         */
        LineOrigin of(Cutting cutting, Optional<WhereAPartDecides> part,
                      AuthoredPointMapping authored);
    }

    /**
     * The geometry {@code assessed} adds, with {@code originOf} answering where a line drawn on
     * one cutting comes from.
     */
    static ComparisonGeometry of(ComparisonAssessment assessed, OriginOf originOf) {
        if (!(assessed instanceof ComparisonAssessment.Several several)) {
            return ofALine(assessed,
                    (cutting, authored) -> originOf.of(cutting, Optional.empty(), authored));
        }
        // What each of its lines adds, once for each case where it decides — each a reading of the
        // line, whose origin says which line it is and which case it is read in.
        List<LineEvidence> evidence = new ArrayList<>();
        List<LineDrawn> between = new ArrayList<>();
        for (ComparisonAssessment.Several.Part part : several.parts()) {
            for (WhereAPartDecides reading : part.readings()) {
                ComparisonGeometry line = ofALine(part.line(),
                        (cutting, authored) -> originOf.of(cutting, Optional.of(reading),
                                authored));
                evidence.addAll(line.evidence());
                between.addAll(line.between());
            }
        }
        return new ComparisonGeometry(evidence, between);
    }

    /** What one line adds, its origin answered by {@code originOf}. */
    private static ComparisonGeometry ofALine(
            ComparisonAssessment assessed,
            BiFunction<Cutting, AuthoredPointMapping, LineOrigin> originOf) {
        return switch (assessed) {
            case ComparisonAssessment.AtAPosition at ->
                    atAPosition(at, originOf.apply(at.cutting(), at.authored()));
            // A value singled out on such a quantity is a line as an order is, where the quantity
            // counts: no position holds it as a class, so the line is where the rule is measured.
            // And each line parting values that settle the relation is a line on its position.
            case ComparisonAssessment.AcrossPositions over -> {
                List<LineDrawn> between = over.drawsABorder()
                        ? List.of(new LineDrawn(over.cutting(),
                                originOf.apply(over.cutting(), over.authored())))
                        : List.of();
                yield new ComparisonGeometry(List.of(), between)
                        .with(settling(over.settling(), originOf));
            }
            // A relation against another value is no line, and each line parting values that
            // settle it is one on its position.
            case ComparisonAssessment.AgainstAnotherValue against ->
                    settling(against.settling(), originOf);
            case ComparisonAssessment.Several _ -> throw new IllegalArgumentException(
                    "a line of a statement is one line: " + assessed);
            case ComparisonAssessment.AnswerDependent _,
                 ComparisonAssessment.OnADependencysAnswer _,
                 ComparisonAssessment.StatesNoRelation _, ComparisonAssessment.NoInput _,
                 ComparisonAssessment.CutsNothing _, ComparisonAssessment.OutsideTheDomain _,
                 ComparisonAssessment.NothingArrivesAtItsLine _,
                 ComparisonAssessment.TurnsNothing _,
                 ComparisonAssessment.NothingArrivesAtItsRelation _,
                 ComparisonAssessment.RelationTurnsNothing _,
                 ComparisonAssessment.NoFeasibleInput _, ComparisonAssessment.Unread _ -> NONE;
        };
    }

    /** What each of {@code lines}, each parting values that settle a relation, adds. */
    private static ComparisonGeometry settling(
            List<ComparisonAssessment.AtAPosition> lines,
            BiFunction<Cutting, AuthoredPointMapping, LineOrigin> originOf) {
        ComparisonGeometry out = NONE;
        for (ComparisonAssessment.AtAPosition each : lines) {
            out = out.with(atAPosition(each, originOf.apply(each.cutting(), each.authored())));
        }
        return out;
    }

    /** This and {@code more} together. */
    private ComparisonGeometry with(ComparisonGeometry more) {
        List<LineEvidence> allEvidence = new ArrayList<>(evidence);
        allEvidence.addAll(more.evidence());
        List<LineDrawn> allBetween = new ArrayList<>(between);
        allBetween.addAll(more.between());
        return new ComparisonGeometry(allEvidence, allBetween);
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
