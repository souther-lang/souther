package souther.compiler.query;

import souther.compiler.claims.ClaimVerdict;
import souther.compiler.claims.Claims;
import souther.compiler.inputs.Unsettlement;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What a report says about the claims a body makes, added to a measure that was made without them.
 *
 * <p>The class boundary is the guarantee. What a row is owed at is counted with no claim in scope
 * — {@link Coverages} names nothing of this — and what a body declared is put beside those numbers
 * here, afterwards, where it can only add lines to a report. Written as one pass over both, the
 * discipline would be a rule somebody has to keep at each place a denominator is counted; written
 * as two, a claim narrowing one is a change to this file's inputs and shows up as such.
 *
 * <p>Nothing here reaches a diagnostic either. A claim the model's own rules contradict is refused
 * where the body is checked; what arrives here is a claim the rules bore out and one nothing
 * settled.
 */
final class ClaimReport {

    /**
     * The same evidence, saying what the body claimed about the positions it counts and about the
     * positions it has no axis for.
     *
     * <p>Takes the module's check rather than one behavior's claims, so that the code counting a
     * denominator never holds a claim at all: what it hands over is what it already had.
     */
    static PartitionEvidence decorate(PartitionEvidence measured, Bodies.Elaborated checked,
                                      String behavior) {
        Claims claims = checked == null ? Claims.NONE
                : checked.claims().getOrDefault(behavior, Claims.NONE);
        if (claims.isEmpty()) {
            return measured;
        }
        List<PartitionEvidence.AxisCoverage> axes = new ArrayList<>();
        Set<String> spokenFor = new LinkedHashSet<>();
        for (PartitionEvidence.AxisCoverage axis : measured.axes()) {
            spokenFor.add(axis.path());
            axes.add(saying(axis, claims));
        }
        return new PartitionEvidence(PartitionEvidence.Partitioned.of(axes), measured.bounded(),
                measured.pairs(), measured.notDerivable(), measured.unread(), measured.omitted(),
                offAxis(claims, spokenFor), measured.whyUnclassified());
    }

    /**
     * One axis, with what the body claimed about the position it measures.
     *
     * <p>A confirmed claim names a case the rules already took out of the classes, so what it adds
     * is the author's own words for why; an unproven one names a case that is still counted, and
     * says that nothing settled it.
     */
    private static PartitionEvidence.AxisCoverage saying(PartitionEvidence.AxisCoverage axis,
                                                         Claims claims) {
        List<PartitionEvidence.ExcludedClass> ruled = new ArrayList<>();
        List<PartitionEvidence.UnprovenClaim> unproven = new ArrayList<>();
        for (Claims.Judged judged : claims.all()) {
            if (!judged.claim().at().toString().equals(axis.path())) {
                continue;
            }
            String named = judged.claim().named().name();
            switch (judged.verdict()) {
                case ClaimVerdict.Confirmed _ -> ruled.add(
                        new PartitionEvidence.ExcludedClass(named, judged.claim().reasons()));
                case ClaimVerdict.Unproven un -> unproven.add(
                        new PartitionEvidence.UnprovenClaim(named, judged.claim().reasons(),
                                said(un.why())));
                // Refused where it is written, so a report of this model is a report of one that
                // did not compile.
                case ClaimVerdict.Contradicted _ -> { }
            }
        }
        return ruled.isEmpty() && unproven.isEmpty() ? axis
                : new PartitionEvidence.AxisCoverage(axis.axis(), axis.path(), axis.classes(),
                        axis.covered(), ruled, unproven, axis.unclassifiedRows(), axis.status(),
                        axis.reason());
    }

    /**
     * The claims about positions no axis here speaks for.
     *
     * <p>A position past the axis limit is dropped and one deeper than the walk goes is never read,
     * and a claim about either was judged all the same. Said here, so that what a report knows about
     * a claim does not turn on whether the position it is about made it into the numbers.
     */
    private static List<PartitionEvidence.ClaimOffAxis> offAxis(Claims claims,
                                                                Set<String> spokenFor) {
        List<PartitionEvidence.ClaimOffAxis> out = new ArrayList<>();
        for (Claims.Judged judged : claims.all()) {
            String at = judged.claim().at().toString();
            if (spokenFor.contains(at)) {
                continue;
            }
            String named = judged.claim().named().name();
            switch (judged.verdict()) {
                case ClaimVerdict.Confirmed _ -> out.add(new PartitionEvidence.ClaimOffAxis(
                        at, named, judged.claim().reasons(), null));
                case ClaimVerdict.Unproven un -> out.add(new PartitionEvidence.ClaimOffAxis(
                        at, named, judged.claim().reasons(), said(un.why())));
                case ClaimVerdict.Contradicted _ -> { }
            }
        }
        return List.copyOf(out);
    }

    /** What a reader is told about a claim nothing settled. One projection, so that a distinction
     *  this compiler learns to make later is a word the report chooses to add rather than one it
     *  gains by accident. */
    private static PartitionEvidence.UnprovenClaim.Why said(Unsettlement why) {
        return switch (why) {
            case Unsettlement.ReadingStopped _ ->
                    PartitionEvidence.UnprovenClaim.Why.A_RULE_WENT_UNREAD;
            case Unsettlement.RulesLeaveNothing _ ->
                    PartitionEvidence.UnprovenClaim.Why.THE_RULES_LEAVE_THE_POSITION_NOTHING;
            case Unsettlement.NoSuchDistinction _ ->
                    PartitionEvidence.UnprovenClaim.Why.NOTHING_WAS_READ_ABOUT_THE_CASE;
            case Unsettlement.ForkNotKnownToBeReached _ ->
                    PartitionEvidence.UnprovenClaim.Why.THE_FORK_IS_NOT_KNOWN_TO_BE_REACHED;
        };
    }

    private ClaimReport() {}
}
