package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.check.TypeChecker;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Numbering the arms of a body, before anything is measured with them.
 *
 * <p>The numbering has to be a property of the body and nothing else. If it moved with the example
 * rows, or with which arm happened to be asked about first, a coverage report could not be compared
 * against the one before it, and the author would be told a branch appeared when nothing changed.
 */
class CoverageSitesTest {

    private static final String MODEL = """
            module example.leave

            data UnderThirty
            data ThirtyOrOver
            data AgeBand = UnderThirty | ThirtyOrOver

            data Days = Int invariant value >= 90 && value <= 330

            behavior daysFor : (age: AgeBand, senior: Bool) -> Days
                constructs Days

            let daysFor (age, senior) =
                match age with
                    | UnderThirty ->
                        if senior then Days(120) else Days(90)
                    | ThirtyOrOver ->
                        unreachable "a member over thirty is handled elsewhere"
            """;

    private static Map<String, Core> bodiesOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        TypeChecker.Checked checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        return checked.behaviorBodies();
    }

    private static CoverageSites.Plan planOf(String source) {
        return CoverageSites.of("leave.sou", bodiesOf(source));
    }

    private static List<String> labels(CoverageSites.Plan plan) {
        return plan.sites().stream().map(CoverageSites.Site::label).toList();
    }

    @Test
    void everyArmOfEveryForkIsASiteAndNothingElseIs() {
        CoverageSites.Plan plan = planOf(MODEL);

        assertEquals(List.of("case UnderThirty", "then", "else", "case ThirtyOrOver"), labels(plan));
        assertEquals(List.of(CoverageSites.Site.Kind.CASE, CoverageSites.Site.Kind.THEN,
                        CoverageSites.Site.Kind.ELSE, CoverageSites.Site.Kind.CASE),
                plan.sites().stream().map(CoverageSites.Site::kind).toList());
    }

    /** Reaching one is already an error, so a probe there would leave a correct model one arm short
     * for ever and make every denominator wrong. */
    @Test
    void anUnreachableArmIsNotCounted() {
        CoverageSites.Plan plan = planOf(MODEL);

        assertTrue(plan.sites().stream().noneMatch(s -> s.label().contains("unreachable")));
        assertEquals(4, plan.sites().size(),
                "the `ThirtyOrOver` case is a site; what it answers with is not");
    }

    @Test
    void aGuardKeepsBothOfItsArmsTogether() {
        CoverageSites.Plan plan = planOf(MODEL);

        assertEquals(1, plan.guards().size());
        CoverageSites.GuardRef guard = plan.guards().get(0);
        assertEquals("then", plan.site(guard.siteIndexThen()).label());
        assertEquals("else", plan.site(guard.siteIndexElse()).label());
    }

    @Test
    void aSiteIsFoundByTheNodeInstanceTheEmitterHolds() {
        Map<String, Core> bodies = bodiesOf(MODEL);
        CoverageSites.Plan plan = CoverageSites.of("leave.sou", bodies);

        Core body = bodies.get("daysFor");
        Core.Match match = (Core.Match) unwrap(body);
        int[] arms = plan.probesOf(match);
        assertNotNull(arms, "the plan is keyed by the instances it was built from");
        assertEquals(2, arms.length);
        assertEquals("case UnderThirty", plan.site(arms[0]).label());

        Core.Match copy = new Core.Match(match.scrutinee(), match.cases(), match.type(),
                match.pos());
        assertEquals(match, copy, "an equal node is easy to make");
        assertNull(plan.probesOf(copy),
                "and it is not this one: a value-keyed plan would hand the emitter another arm's probe");
    }

    /** A body's arms are its own. Rows do not move them, and neither does anything above them. */
    @Test
    void theNumberingDependsOnTheBodyAndNothingElse() {
        List<String> without = labels(planOf(MODEL));
        List<String> withRows = labels(planOf(MODEL + """

                example daysFor
                    | (UnderThirty, true)  -> Days(120)
                    | (UnderThirty, false) -> Days(90)
                """));

        assertEquals(without, withRows);
        assertEquals(labels(planOf(MODEL)), without, "and it is the same on a second walk");
    }

    @Test
    void anArmsFingerprintIgnoresWhereItIsWritten() {
        String moved = MODEL.replace("module example.leave\n",
                "module example.leave\n\n// a comment that pushes everything down\n");

        assertEquals(planOf(MODEL).sites().stream().map(CoverageSites.Site::fingerprint).toList(),
                planOf(moved).sites().stream().map(CoverageSites.Site::fingerprint).toList());
    }

    /**
     * The known limit of a content fingerprint: two arms made of the same thing share one. Recorded
     * here so that whatever matches one run against another later does not assume otherwise.
     */
    @Test
    void twoArmsMadeOfTheSameThingShareAFingerprint() {
        CoverageSites.Plan plan = planOf("""
                module example.same

                data Yes
                data No
                data Answer = Yes | No

                data Score = Int

                behavior scoreFor : (a: Answer, b: Answer) -> Score
                    constructs Score

                let scoreFor (a, b) =
                    match a with
                        | Yes -> match b with
                                     | Yes -> Score(1)
                                     | No  -> Score(0)
                        | No  -> match b with
                                     | Yes -> Score(1)
                                     | No  -> Score(0)
                """);

        List<String> inner = plan.sites().stream()
                .filter(s -> s.label().equals("case Yes"))
                .map(CoverageSites.Site::fingerprint).toList();
        assertTrue(inner.size() > inner.stream().distinct().count(),
                "two arms with the same shape and label collide, which is why index is identity here");
    }

    private static Core unwrap(Core body) {
        Core at = body;
        while (at instanceof Core.Block block) {
            at = block.body();
        }
        return at;
    }

    @Test
    void aModuleWithNoBodiesPlansNothing() {
        assertSame(true, CoverageSites.of("x.sou", Map.of()).isEmpty());
    }
}
