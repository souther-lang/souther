package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.types.SourceConstructOrigin;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which arm a run went through is read off the sites it passed, and the rewrite of that arm stands
 * at every site of it.
 *
 * <p>A helper spliced into two places is one arm at two sites. A run through one of them asks about
 * the arm the author wrote, and that arm rewritten is rewritten wherever it was spliced — as an edit
 * of the source would be — and not only where this run happened to pass.
 */
class ARewriteThroughAnArmStandsAtEverySiteOfItTest {

    private static final SourceConstructOrigin FORK = SourceConstructOrigin.unwritten();

    private static final ArmReplacements.Differs PARTS = ArmReplacements.Differs.ALWAYS;

    /** Arm 0 of the fork at sites 3 and 7, arm 1 at sites 4 and 8, each carrying the other. */
    private static ArmReplacements spliced() {
        TreeMap<Integer, ArmReplacements.AtSite> bySite = new TreeMap<>();
        bySite.put(3, new ArmReplacements.AtSite(FORK, 0,
                Map.of(1, new ArmReplacements.Sibling.Carried(PARTS))));
        bySite.put(4, new ArmReplacements.AtSite(FORK, 1,
                Map.of(0, new ArmReplacements.Sibling.Carried(PARTS))));
        bySite.put(7, new ArmReplacements.AtSite(FORK, 0,
                Map.of(1, new ArmReplacements.Sibling.Carried(PARTS))));
        bySite.put(8, new ArmReplacements.AtSite(FORK, 1,
                Map.of(0, new ArmReplacements.Sibling.Carried(PARTS))));
        return new ArmReplacements(bySite);
    }

    @Test
    void aRunThroughOneSiteAsksForTheArmRewrittenAtEverySite() {
        List<ArmReplacements.Rewrite> asked = spliced().through(Set.of(3));

        assertEquals(1, asked.size(), "one arm, one sibling: " + asked);
        assertEquals(Map.of(3, 1, 7, 1), asked.getFirst().replacing(),
                "the sibling stands at both sites of the arm");
    }

    @Test
    void aRunThroughBothSitesAsksForTheRewriteOnce() {
        assertEquals(1, spliced().through(Set.of(3, 7)).size(),
                "two sites of one arm are one rewrite");
    }

    /**
     * What a recording is run again under: at a site that carries the sibling, the sibling
     * standing wherever it is carried; at a site that does not, nothing.
     */
    @Test
    void aRecordingIsRunAgainOnlyWhereTheSitePassedCarriesTheSibling() {
        ArmReplacements partly = spliced().carryingNothingAt(Set.of(7));

        assertEquals(Map.of(3, 1), partly.through(Set.of(3)).getFirst().replacing());
        assertEquals(List.of(), partly.through(Set.of(7)),
                "a run through the site carrying nothing asks for nothing there");
    }

    @Test
    void aRewriteEverySiteCarriesIsAskedAndRunsAtEverySite() {
        assertEquals(List.of(new ArmReplacements.Asked.Runs(new ArmReplacements.Rewrite(FORK, 0, 1,
                        new TreeMap<>(Map.of(3, 1, 7, 1))))),
                spliced().askedOf(FORK, 0, _ -> false));
    }

    /**
     * A rewrite some site of the arm does not carry is no run of the arm rewritten, whichever site
     * a row went through: run at the sites that carry it, the site the row passed may answer as
     * written, and the row would be asked about a program nobody can write.
     */
    @Test
    void aRewriteSomeSiteDoesNotCarryIsAskedAndNotRun() {
        ArmReplacements partly = spliced().carryingNothingAt(Set.of(7));

        assertEquals(List.of(new ArmReplacements.Asked.NotRun(1,
                        new ArmReplacements.Sibling.Why.PastWhatAMethodHolds())),
                partly.askedOf(FORK, 0, _ -> false));
    }

    /** A sibling that parts from the arm on no way is the arm under another spelling. */
    @Test
    void aSiblingThatPartsOnNoWayIsNotAsked() {
        TreeMap<Integer, ArmReplacements.AtSite> bySite = new TreeMap<>();
        bySite.put(3, new ArmReplacements.AtSite(FORK, 0,
                Map.of(1, new ArmReplacements.Sibling.Carried(ArmReplacements.Differs.NEVER))));

        assertEquals(List.of(),
                new ArmReplacements(bySite).askedOf(FORK, 0, _ -> false));
    }

    /**
     * Every rewrite a row through a site is asked has a run among those its recording is run again
     * under, which is what the measure of a written row reads its answer from.
     */
    @Test
    void everyRewriteARowIsAskedIsOneItsRecordingIsRunAgainUnder() {
        for (ArmReplacements carried : List.of(spliced(), spliced().carryingNothingAt(Set.of(7)))) {
            for (int site : carried.bySite().keySet()) {
                ArmReplacements.AtSite at = carried.bySite().get(site);
                List<ArmReplacements.Rewrite> run = carried.through(Set.of(site));
                for (ArmReplacements.Asked each
                        : carried.askedOf(at.fork(), at.part(), _ -> false)) {
                    if (each instanceof ArmReplacements.Asked.Runs(var rewrite)) {
                        assertTrue(run.contains(rewrite),
                                () -> rewrite + " is asked at site " + site + ", run: " + run);
                    }
                }
            }
        }
    }
}
