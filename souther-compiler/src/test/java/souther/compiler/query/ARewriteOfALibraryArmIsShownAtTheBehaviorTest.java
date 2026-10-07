package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.Citation;
import souther.compiler.diag.Located;
import souther.compiler.diag.Messages;
import souther.compiler.meta.ModulePath;
import souther.compiler.partition.Replacement;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rewrite of an arm is shown where the arm it rewrites would be shown: at the fork when this
 * compilation holds the source the fork is written in, and at the behavior when it does not.
 *
 * <p>The language's own helpers are written in sources, so the construct a fork of theirs comes from
 * says it was written; what it does not say is whether this compilation holds that source. Asked of
 * the construct, a rewrite of an arm of {@code Int.max} was sent to a file nobody here has, and the
 * build stopped there. The rows below state the constructor and not what it holds, so a rewrite of
 * the helper's arm answers differently and no row comes out differently under it.
 */
class ARewriteOfALibraryArmIsShownAtTheBehaviorTest {

    private static final String LIMITS = """
            module shop.limits exposing ( atLeastNone )

            let atLeastNone (n: Int): Int = if n > 0 then n else 0
            """;

    private static final String ORDERS = """
            module shop.orders

            import shop.limits ( atLeastNone )

            data Kept = { n: Int }
            data Dropped
            data Outcome = Kept | Dropped

            behavior keepHere : (n: Int) -> Outcome

            let keepHere (n) = if n > 100 then Dropped else Kept { n = atLeastNone(n) }

            example keepHere
                | "a small number is kept" : (5) -> Kept
                | "a negative number is kept" : (-3) -> Kept
                | "a large number is dropped" : (200) -> Dropped

            behavior keepInTheLibrary : (n: Int, m: Int) -> Outcome

            let keepInTheLibrary (n, m) =
                if n > 100 then Dropped else Kept { n = Int.max(n, 0) + Int.max(m, 0) }

            example keepInTheLibrary
                | "small numbers are kept" : (5, 5) -> Kept
                | "negative numbers are kept" : (-3, -3) -> Kept
                | "a large number is dropped" : (200, 0) -> Dropped
            """;

    private static Compilation measured() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("limits.sou", LIMITS);
        byId.put("orders.sou", ORDERS);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        c.answerEverything();
        assertEquals(List.of(), c.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return c;
    }

    /** The rewrites of arms of {@code behavior} no row tells apart, as findings. */
    private static List<Adequacy.Finding> armRewritesOf(Compilation c, String behavior) {
        return Adequacy.accountOf(c.db(), "shop.orders").stream()
                .filter(each -> each.about() instanceof About.ARewriteNoRowTellsApart rewrite
                        && rewrite.behavior().equals(behavior)
                        && rewrite.replacement() instanceof Replacement.OfAnArm)
                .toList();
    }

    @Test
    void aRewriteOfAnArmOfTheLanguageIsShownAtTheBehavior() {
        Compilation c = measured();
        List<Adequacy.Finding> rewrites = armRewritesOf(c, "keepInTheLibrary");
        assertFalse(rewrites.isEmpty(), () -> "a row answers differently when an arm of `Int.max`"
                + " answers as its sibling, and none comes out differently: "
                + Adequacy.accountOf(c.db(), "shop.orders"));

        Citation behavior = c.db().ask(
                new Sites.WhereABehaviorIsDeclared("shop.orders", "keepInTheLibrary")).value();
        for (Adequacy.Finding each : rewrites) {
            About.ARewriteNoRowTellsApart about = (About.ARewriteNoRowTellsApart) each.about();
            Replacement.OfAnArm arm = (Replacement.OfAnArm) about.replacement();
            assertEquals("souther.int", arm.fork().module(), "the fork is the language's");
            assertInstanceOf(ReplacementReportAnchor.AtTheBehavior.class, about.reportAt(),
                    "and this compilation holds no source of it");
            assertEquals(behavior, Adequacy.placeOf(c.db(), "shop.orders", each),
                    "so it is shown at the behavior");
        }
    }

    @Test
    void aRewriteOfAnArmWrittenHereIsShownAtTheFork() {
        Compilation c = measured();
        List<Adequacy.Finding> rewrites = armRewritesOf(c, "keepHere");
        assertFalse(rewrites.isEmpty(), () -> "a row answers differently when an arm of the helper"
                + " answers as its sibling, and none comes out differently: "
                + Adequacy.accountOf(c.db(), "shop.orders"));

        for (Adequacy.Finding each : rewrites) {
            About.ARewriteNoRowTellsApart about = (About.ARewriteNoRowTellsApart) each.about();
            assertInstanceOf(ReplacementReportAnchor.AtTheFork.class, about.reportAt(),
                    "the helper is written in a file this compilation holds");
            Citation.Written shown = assertInstanceOf(Citation.Written.class,
                    Adequacy.placeOf(c.db(), "shop.orders", each));
            assertEquals(3, c.texts().resolve(shown.at()).line(),
                    "which is the line the `if` is on in limits.sou, not the call in orders.sou");
        }
    }

    /**
     * Two calls of one helper reach its fork at two places, and an arm of it rewritten as a sibling
     * is still one program. Shown at the call, it would be one rewrite per call.
     */
    @Test
    void twoCallsOfOneLibraryHelperAreOneRewriteOfEachArm() {
        Compilation c = measured();
        List<CoverageSites.ArmSite> reached = c.db().ask(new Bodies.Checked("shop.orders"))
                .value().plan().arms("keepInTheLibrary").stream()
                .filter(each -> "souther.int".equals(each.obligation().origin().module()))
                .toList();
        Set<Object> arms = new HashSet<>();
        reached.forEach(each -> arms.add(List.of(each.obligation().origin(),
                each.obligation().part())));
        assertTrue(reached.size() > arms.size(), () -> "both calls reach the helper's fork: "
                + reached);

        ReplacementEvidence evidence = c.db().ask(new Replacements.Measured("shop.orders"))
                .value().get("keepInTheLibrary");
        List<ReplacementEvidence.Rewrite> ofTheLanguage = evidence.measured().made().orElseThrow()
                .rewrites().stream()
                .filter(each -> each.replacement() instanceof Replacement.OfAnArm arm
                        && "souther.int".equals(arm.fork().module()))
                .toList();
        assertFalse(ofTheLanguage.isEmpty(), "the helper's arms are rewritten");
        assertEquals(ofTheLanguage.size(), ofTheLanguage.stream()
                        .map(ReplacementEvidence.Rewrite::replacement).distinct().count(),
                () -> "each rewrite once, whichever call reached it: " + ofTheLanguage);
        assertTrue(ofTheLanguage.stream().allMatch(each ->
                        each.reportAt() instanceof ReplacementReportAnchor.AtTheBehavior),
                () -> "and every one of them shown at the behavior: " + ofTheLanguage);
    }

    /** The sentence says which arm, since the behavior it is pointed at is not one. */
    @Test
    void theBuildIsToldTheArmIsInCodeItHoldsNoSourceOf() {
        Compilation c = measured();
        List<String> said = c.warnings().stream()
                .map(Located::diagnostic)
                .filter(d -> "E1939".equals(d.code().toString()))
                .map(d -> Messages.render(d.said(), Locale.ENGLISH))
                .toList();

        assertTrue(said.contains("No row of `keepInTheLibrary` would come out differently if an"
                        + " arm it reaches in code this build holds no source of answered as"
                        + " another arm of its fork."),
                () -> "what a build is told: " + said);
        assertTrue(said.contains("No row of `keepHere` would come out differently if this arm"
                        + " answered as another arm of its fork."),
                () -> "and the arm a reader can open is this one: " + said);
    }
}
