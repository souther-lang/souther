package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.InputCaseEvidence;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.query.Weakening;
import souther.compiler.query.WeakeningSet;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a whole went without holds everything its parts went without.
 *
 * <p>Stronger than the rule beside it. {@code AMeasurementIsNeverStrongerThanWhatItIsAssembledFrom}
 * asks whether the words agree — a complete whole over a partial part is a contradiction — and a
 * whole that kept its own word while dropping a part's account of why passes it: both say
 * {@code partial}, and the fact that made one of them so is gone. The word was never the point.
 *
 * <p>So this asks the union. A parent's weakening is the union of its parts' and nothing else, which
 * is the whole of the arithmetic #953 replaced a lattice with, and the one property that makes the
 * arithmetic worth having: a fact reaching a whole by any path arrives, and a producer that forgets
 * to hand one over is a whole that is short of it.
 *
 * <p>Held over the values rather than over the document, because the document is where a fact can go
 * missing without anything else moving. The projection is checked where it is written
 * ({@code AMeasureWeakerThanCompleteSaysWhatMadeItSo}); this is about what it is given.
 */
class WhatAWholeWentWithoutIsWhatItsPartsWentWithoutTest {

    /**
     * A model whose rows are seen in part, whose rules are read in part, and one of whose behaviors
     * nobody wrote a row for.
     *
     * <p>Each is a different way for a fact to arrive, and a whole that dropped one of them is what
     * this is looking for — so a model producing only one kind would hold the rule over one path
     * and say nothing about the rest.
     */
    private static final String MODEL = """
            module example.whole

            data Draft = { n: Int }
            data Done = { n: Int }
            data Small = { n: Int }
            data Assignee = String
                invariant String.length(value) >= 1
            data Issue = { assignee: Assignee? }

            partial let spin (n: Int): Int = spin(n)

            behavior go : (request: Draft) -> Done | Small
                constructs Done, Small

            let go (request) = {
                guard request.n <= 0 else Done { n = spin(request.n) }
                Small { n = request.n }
            }

            behavior classify : (i: Issue) -> Done
            behavior unwritten : (request: Draft) -> Done | Small
                constructs Done, Small

            example go
                | (Draft { n = 1 }) -> Done { n = 1 }
            """;

    private static AdequacyReport report() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    @Test
    void everyWholeHoldsWhatEachOfItsPartsWentWithout() {
        AdequacyReport report = report();
        List<String> lost = new ArrayList<>();
        Set<Weakening> everything = new LinkedHashSet<>();
        int loadBearing = 0;

        WeakeningSet acrossModules = WeakeningSet.none();
        for (AdequacyReport.ModuleReport module : report.modules()) {
            WeakeningSet acrossBehaviors = WeakeningSet.none();
            for (AdequacyReport.BehaviorReport behavior : module.behaviors()) {
                WeakeningSet parts = WeakeningSet.none();
                List<WeakeningSet> apart = new ArrayList<>();

                if (behavior.signature() != null) {
                    Adequacy.SignatureEvidence signature = behavior.signature();
                    WeakeningSet cases = signature.output().cases().weakening();
                    for (InputCaseEvidence each : signature.inputs()) {
                        cases = cases.union(each.cases().weakening());
                    }
                    holds(lost, "signature of " + behavior.name(),
                            signature.counted().weakening(), cases);
                    parts = parts.union(signature.counted().weakening());
                    apart.add(signature.counted().weakening());
                }
                if (behavior.branch() != null) {
                    parts = parts.union(behavior.branch().measured().weakening());
                    apart.add(behavior.branch().measured().weakening());
                }
                if (behavior.partition() != null) {
                    PartitionEvidence partition = behavior.partition();
                    parts = parts.union(partition.partitioned().weakening())
                            .union(partition.bounded().weakening())
                            .union(partition.pairs().counted().weakening());
                    for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
                        parts = parts.union(axis.reached().weakening());
                    }
                    for (BorderAssessment.Point point
                            : BorderAssessment.pointsOf(partition.boundaries())) {
                        parts = parts.union(point.item().weakening());
                    }
                    apart.add(partition.partitioned().weakening());
                    apart.add(partition.bounded().weakening());
                    apart.add(partition.pairs().counted().weakening());
                }
                loadBearing += loadBearing(apart);
                holds(lost, "behavior " + behavior.name(), behavior.weakenedBy(), parts);
                acrossBehaviors = acrossBehaviors.union(behavior.weakenedBy());
            }
            holds(lost, "module " + module.module(), module.weakenedBy(), acrossBehaviors);
            acrossModules = acrossModules.union(module.weakenedBy());
            everything.addAll(module.weakenedBy().causes());
        }
        holds(lost, "the report", report.weakenedBy(), acrossModules);

        // And the run reached each way a fact arrives, so the rule above was held over every path
        // rather than over whichever one this model happened to take.
        Set<String> kinds = new LinkedHashSet<>();
        everything.forEach(each -> kinds.add(each.getClass().getSimpleName()));
        assertTrue(kinds.contains("ObservationIncomplete") && kinds.contains("ModelReadingIncomplete")
                        && kinds.size() >= 3,
                () -> "the model reaches every way a measure goes without something: " + kinds);

        // And at least one part carries a fact no other part of its behavior does, so the rule
        // above is not one a whole satisfies whatever it drops. A union is a set: a part left out
        // of it goes unnoticed for as long as something else happens to carry the same fact, and a
        // fixture in which no part is load-bearing holds this rule over nothing at all.
        assertTrue(loadBearing > 0,
                "no part of any behavior went without anything the rest did not, so dropping any"
                        + " one of them from the union would leave this saying nothing");

        assertEquals(List.of(), lost, "a whole and its parts disagreeing about what was gone without");
    }

    /** How many of {@code parts} hold a fact none of the others do. */
    private static int loadBearing(List<WeakeningSet> parts) {
        int carrying = 0;
        for (int i = 0; i < parts.size(); i++) {
            Set<Weakening> rest = new LinkedHashSet<>();
            for (int j = 0; j < parts.size(); j++) {
                if (i != j) {
                    rest.addAll(parts.get(j).causes());
                }
            }
            if (parts.get(i).causes().stream().anyMatch(one -> !rest.contains(one))) {
                carrying++;
            }
        }
        return carrying;
    }

    /**
     * What {@code whole} carries and what {@code parts} went without, held to being the same.
     *
     * <p>Both ways round, because the rule is a union and nothing else. Short of what its parts went
     * without, a whole has dropped a fact somebody is owed; over it, a whole has a fact none of its
     * parts has — which is the shape the report was in when it read the module's own list of what
     * could not be read and made weakenings out of it beside asking the measures. One of those is
     * the defect this issue is about and the other is how it hid.
     */
    private static void holds(List<String> lost, String what, WeakeningSet whole,
                              WeakeningSet parts) {
        for (Weakening each : parts.causes()) {
            if (!whole.causes().contains(each)) {
                lost.add(what + " does not carry " + each + ", which one of its parts went without");
            }
        }
        for (Weakening each : whole.causes()) {
            if (!parts.causes().contains(each)) {
                lost.add(what + " carries " + each + ", which none of its parts went without");
            }
        }
    }
}
