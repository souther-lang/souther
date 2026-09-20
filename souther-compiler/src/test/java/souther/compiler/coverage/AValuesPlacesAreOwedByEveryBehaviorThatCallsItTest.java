package souther.compiler.coverage;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.query.Bodies;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The places a value's method holds are owed by every behavior that calls it.
 *
 * <p>A value emitted as a method of its own is one body with one set of probes, however many
 * behaviors call it. The places are counted once and each caller owes them, so what a behavior is
 * asked of — its comparisons, its arms — includes what the values it calls compare and fork on, as
 * it does where the same expression is written in the behavior.
 */
class AValuesPlacesAreOwedByEveryBehaviorThatCallsItTest {

    private static final String SHARED = """
            module m exposing (f, g, h)

            let big = if List.length([1, 2, 3]) > 2 then 1 else 0

            behavior f : (n: Int) -> Int
            let f (n) = if n > 0 then big else 0

            behavior g : (n: Int) -> Int
            let g (n) = if n > 1 then big else 0

            behavior h : (n: Int) -> Int
            let h (n) = if n > 2 then 5 else 0
            """;

    private static CoverageSites.Plan plan() {
        return Compiler.compiled(SHARED, "m").db().ask(new Bodies.Checked("m")).value().plan();
    }

    private static List<ComparisonEmissionSite> comparisonProbes(
            List<CoverageSites.ComparisonSite> sites) {
        return sites.stream().map(CoverageSites.ComparisonSite::index).toList();
    }

    @Test
    void aCallerOwesTheComparisonsAndArmsTheValueItCallsHolds() {
        CoverageSites.Plan plan = plan();

        // `f` writes one comparison and one fork of its own, and `big` writes one of each.
        assertEquals(2, plan.comparisons("f").size(), "the comparison in `big` is owed by `f`");
        assertEquals(4, plan.arms("f").size(), "the arms of `big`'s fork are owed by `f`");
    }

    /**
     * One probe and two items owed: what a row that passes the arm answers for is the behavior it
     * was written for, and not every behavior that shares the value.
     */
    @Test
    void twoCallersOweTheSameArmAsTwoObligationsOverOneProbe() {
        CoverageSites.Plan plan = plan();

        CoverageSites.ArmSite ofF = plan.arms("f").stream()
                .filter(arm -> arm.body().equals("big")).findFirst().orElseThrow();
        CoverageSites.ArmSite ofG = plan.arms("g").stream()
                .filter(arm -> arm.body().equals("big")).findFirst().orElseThrow();

        assertEquals(ofF.place(), ofG.place(), "one place, and so one probe");
        assertEquals("f", ofF.obligation().behavior());
        assertEquals("g", ofG.obligation().behavior());
        assertNotEquals(ofF.obligation(), ofG.obligation(),
                "and two items owed, which nothing that deduplicates them may treat as one");
    }

    @Test
    void aBehaviorThatCallsNoValueOwesOnlyItsOwn() {
        CoverageSites.Plan plan = plan();

        assertEquals(1, plan.comparisons("h").size());
        assertEquals(2, plan.arms("h").size());
    }

    @Test
    void twoCallersOweOneSetOfPlacesAndNotTwo() {
        CoverageSites.Plan plan = plan();

        List<ComparisonEmissionSite> ofF = comparisonProbes(plan.comparisons("f"));
        List<ComparisonEmissionSite> ofG = comparisonProbes(plan.comparisons("g"));

        assertFalse(ofF.isEmpty());
        // What each writes for itself differs, and what `big` writes is the same probe in both.
        long shared = ofF.stream().filter(ofG::contains).count();
        assertEquals(1, shared, "one comparison of `big`, numbered once and owed by both callers");
        assertTrue(plan.sites().stream().filter(site -> site.body().equals("big")).count() > 0,
                "and it is numbered as the places of a body of its own");
    }
}
