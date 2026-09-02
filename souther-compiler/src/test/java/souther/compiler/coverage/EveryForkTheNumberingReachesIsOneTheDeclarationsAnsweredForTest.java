package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.CoverageOrigin;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every fork the numbering reaches is one the declarations were read for.
 *
 * <p>Who owns the rule a fork decides by is read off the declarations, and a fork the reading never
 * saw is one it can say neither answer about. It is refused rather than answered, so a gap here
 * stops a build instead of counting every copy of that fork as one — but a refusal is a poor place
 * to find out, and what this is for is finding out before one is written.
 *
 * <p>So the two are held to each other here. A construct that becomes a fork somewhere the reading
 * of the declarations does not look — a lowering that makes forks out of something else, a pass
 * that writes one — is a fork with no entry, and the day one is added this says so rather than the
 * measurement quietly counting its copies as one.
 */
class EveryForkTheNumberingReachesIsOneTheDeclarationsAnsweredForTest {

    private static final String MODULE = "example.every";

    private static final String MODEL = """
            module example.every

            data Yes
            data No
            data Verdict = Yes | No
            data Count = Int

            let decide (p: (Int) -> Bool, x: Int): Verdict = {
                let q = p
                if q(x) then Yes else No
            }

            let choose (p: (Int) -> Bool, x: Int): List<Int> = [ x | p(x) ]

            let atLeast (limit: Int, x: Int): Verdict = if x >= limit then Yes else No

            behavior every : (a: Int, b: List<Int>) -> Count
                constructs Count
            let every (a, b) = {
                let said = decide(n -> n < 18, a)
                let kept = choose(m -> 18 < m, a)
                if said == Yes then
                    Count(List.length(kept) + List.length(List.filter(k -> k > 0, b)))
                else
                    Count(if atLeast(65, a) == Yes then 1 else 0)
            }

            example every
                | "under the line" : (1, [ 1 ]) -> Count(1)
            """;

    @Test
    void everyForkTheNumberingReachesWasAnsweredFor() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked =
                compilation.db().ask(new Bodies.Checked(MODULE)).value();
        assertNotNull(checked, "the model under test compiles");

        CoverageSites.Plan plan = checked.plan();
        List<CoverageOrigin> forks = new ArrayList<>();
        for (CoverageSites.Site site : plan.sites()) {
            CoverageOrigin origin = site.obligation().origin();
            if (site.isArm() && !forks.contains(origin)) {
                forks.add(origin);
            }
        }
        assertTrue(forks.size() >= 5,
                () -> "the model under test writes forks of every kind this reads: " + forks);

        List<CoverageOrigin> unanswered = forks.stream()
                .filter(fork -> !checked.decisions().byFork().containsKey(fork)).toList();
        assertEquals(List.of(), unanswered,
                () -> "every fork the numbering reaches has an entry: " + unanswered);
    }
}
