package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.types.SourceConstructOrigin;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

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

    /** A site whose classes do not carry the sibling is one the rewrite cannot be run at. */
    @Test
    void aSiteThatDoesNotCarryTheSiblingIsLeftOut() {
        ArmReplacements partly = spliced().carryingNothingAt(Set.of(7));

        assertEquals(Map.of(3, 1), partly.through(Set.of(3)).getFirst().replacing());
        assertEquals(List.of(), partly.through(Set.of(7)),
                "a run through the site carrying nothing asks for nothing there");
    }
}
