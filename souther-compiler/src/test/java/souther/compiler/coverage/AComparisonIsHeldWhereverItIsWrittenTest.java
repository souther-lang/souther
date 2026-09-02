package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which comparisons a body holds, answered once and off the body alone.
 *
 * <p>Where a comparison stands is not what makes it one. A comparison written under a fork's
 * condition, one given a name a line above, and one inside a function value handed to a combinator
 * are the same construct put to three uses, and a reading that found only the first was reading the
 * fork rather than the comparison.
 */
class AComparisonIsHeldWhereverItIsWrittenTest {

    private static Map<String, Core> bodiesOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        return checked.behaviorBodies();
    }

    private static List<String> operatorsIn(String source) {
        return comparisonsIn(bodiesOf(source)).stream().map(each -> each.op().name()).toList();
    }

    /**
     * The comparisons of every body, by walking the bodies and asking the catalog at each node.
     *
     * <p>The traversal is this test's and the membership is the catalog's, which is the split the
     * catalog exists for. A list the catalog handed over would be a second answer to keep in step
     * with {@link ComparisonCatalog#at}, and nothing in the compiler wants one.
     */
    private static List<Core.Binary> comparisonsIn(Map<String, Core> bodies) {
        ComparisonCatalog catalog = catalogOf(bodies);
        List<Core.Binary> out = new ArrayList<>();
        bodies.values().forEach(body -> collect(body, catalog, out));
        return out;
    }

    /** The catalog of {@code bodies}, under a module name this fixture supplies. Which name it is
     *  does not matter here: every question below is of one catalog, and a name only has to tell
     *  one module's comparisons from another's. */
    private static ComparisonCatalog catalogOf(Map<String, Core> bodies) {
        return ComparisonCatalog.of(new ModuleBodies("example", bodies));
    }

    /** The plan of the same, under the same name. */
    private static CoverageSites.Plan planOf(Map<String, Core> bodies) {
        return CoverageSites.of(new ModuleBodies("example", bodies),
                DecisionSources.NONE, SuppliedRules.NONE);
    }

    private static void collect(Core e, ComparisonCatalog catalog, List<Core.Binary> out) {
        if (e instanceof Core.Binary binary && catalog.occurrenceAt(binary).isPresent()) {
            out.add(binary);
        }
        Core.forEachChild(e, child -> collect(child, catalog, out));
    }

    private static final String NAMED_BEFORE_THE_FORK = """
            module example.named

            behavior fee : (a: Int) -> Int

            let fee (a) = {
                let ok = a > 1

                if ok then 1 else 0
            }
            """;

    private static final String INSIDE_A_FUNCTION_VALUE = """
            module example.inside

            behavior positives : (xs: List<Int>) -> List<Int>

            let positives (xs) = List.filter(x -> x > 0, xs)
            """;

    private static final String BEHIND_AN_ABORT = """
            module example.abort

            behavior pick : (a: Int) -> Int

            let pick (a) =
                if a > 10 then
                    (if a > 20 then unreachable "never" else unreachable "nor this")
                else 3
            """;

    /** A comparison a name stands for is a comparison, and the fork below tests the name. */
    @Test
    void aComparisonGivenANameBeforeTheForkIsStillOne() {
        assertEquals(List.of("GT"), operatorsIn(NAMED_BEFORE_THE_FORK));
    }

    /**
     * What combines comparisons is not one, and what answers a number is not one either.
     *
     * <p>The pair this refuses is what keeps the numbering checkable. A probe copies the value off
     * the stack where the comparison left it, so a walk that took {@code a + b} for a comparison
     * would hand the emitter half a {@code long} to copy — and a walk that took the {@code &&} would
     * number the condition in place of the two statements it is built from.
     */
    @Test
    void whatCombinesComparisonsIsNotOneAndNeitherIsArithmetic() {
        assertEquals(List.of("GE", "GT"), operatorsIn("""
                module example.mixed

                behavior total : (a: Int, b: Int) -> Int

                let total (a, b) = if a + b >= 10 && a > 0 then a * b else a - b
                """));
    }

    /**
     * A comparison inside a function value is written in the body that holds the function value.
     *
     * <p>What a combinator does with it — how many times it applies it, and to what — is the
     * combinator's business and changes nothing about where the comparison was written. Left out,
     * the enumeration would stop at a boundary the reading of what the body does walks straight
     * through, which is a disagreement neither side could notice.
     */
    @Test
    void aComparisonInsideAFunctionValueIsOneOfTheBodyThatHoldsIt() {
        assertEquals(List.of("GT"), operatorsIn(INSIDE_A_FUNCTION_VALUE));
    }

    /**
     * A comparison the catalog holds and the plan numbers no site for is a state this can hold.
     *
     * <p>The two are different questions and the answers differ: every comparison of every body is
     * catalogued, and what gets a site is what a run could be recorded at. A comparison behind an
     * abort is one no run reaches, so nothing numbers it — and it is still a comparison the model
     * holds, which is what a reading about it is about.
     *
     * <p>What used to stand here was two tests that a plan is refused when it numbers something the
     * catalog does not hold. Neither state can be built now: a numbering is keyed by which
     * comparison it is, so there is no number to put on a node that is not one, and no way to name
     * a comparison of a body this catalog never walked.
     */
    @Test
    void aComparisonCanBeCataloguedWithNoSiteToRecordARunAt() {
        Map<String, Core> bodies = bodiesOf(BEHIND_AN_ABORT);
        ComparisonCatalog catalog = catalogOf(bodies);
        CoverageSites.Plan plan = planOf(bodies);

        List<ComparisonOccurrence> held = catalog.all().stream()
                .map(ComparisonCatalog.Catalogued::which).toList();
        assertEquals(2, held.size(), "the body holds two comparisons");
        assertEquals(1, held.stream().filter(plan::instruments).count(),
                () -> "and one of them stands where nothing answers, so nothing records a run"
                        + " through it: " + held);
    }

    /**
     * A comparison inside a function value is one a run may pass more than once.
     *
     * <p>Which is why it is numbered rather than why it is not. What a set of places can be asked
     * turns on this, and leaving such a comparison out of the numbering would answer the question by
     * refusing to record the fact — where recording it and marking what it is leaves every reader
     * able to ask.
     */
    @Test
    void aComparisonInsideAFunctionValueMayBePassedMoreThanOnce() {
        Map<String, Core> bodies = bodiesOf("""
                module example.inside

                behavior positives : (xs: List<Int>) -> List<Int>

                let positives (xs) = List.filter(x -> x > 0, xs)
                """);
        CoverageSites.Plan plan = planOf(bodies);
        Core.Binary comparison = comparisonsIn(bodies).get(0);

        assertTrue(plan.comparisons().occurrenceAt(comparison).filter(plan::instruments)
                        .isPresent(), "it is numbered");
        assertTrue(plan.mayRepeat(comparison), "and one run may pass it once per element");
    }

    /**
     * Every comparison a body holds is one the catalog holds.
     *
     * <p>What keeps the two readings one. The catalog gathers what a walk of the bodies recognises
     * and what this compile has source for; a reader that met a comparison the catalog had no name
     * for would have nothing to say which one it was, and the readings would each be complete about
     * a different set. Held here as the property rather than as a check inside the walk, because
     * what it is about is the two definitions agreeing and not one body being odd.
     */
    @Test
    void everyComparisonOfABodyIsOneTheCatalogNames() {
        for (String source : List.of(NAMED_BEFORE_THE_FORK, INSIDE_A_FUNCTION_VALUE, BEHIND_AN_ABORT)) {
            Map<String, Core> bodies = bodiesOf(source);
            ComparisonCatalog catalog = catalogOf(bodies);
            bodies.values().forEach(body -> recognised(body, each ->
                    assertTrue(catalog.occurrenceAt(each).isPresent(),
                            () -> "the catalog names " + each.op() + " at " + each.pos())));
        }
    }

    /**
     * Two comparisons spelled the same way in one body are two occurrences.
     *
     * <p>What an occurrence is for. One comparison as written is spliced into a body once per call
     * of the helper that holds it, so where it is written does not tell the copies apart — they
     * cite one place — and each is reached under its caller's own conditions. A reading that named
     * a comparison by where it is written would have one answer for both, which is what a line
     * drawn on one and a run recorded at the other come to.
     */
    @Test
    void twoComparisonsSpelledAlikeAreTwoOccurrences() {
        Map<String, Core> bodies = bodiesOf("""
                module example.twice

                behavior band : (a: Int) -> Int

                let over (x: Int): Bool = x > 10

                let band (a) = if over(a) then (if over(a) then 1 else 2) else 3
                """);
        ComparisonCatalog catalog = catalogOf(bodies);

        List<ComparisonCatalog.Catalogued> held = catalog.all();
        assertEquals(2, held.size(), "the helper is spliced into the body at both calls");
        assertEquals(held.get(0).at(), held.get(1).at(),
                "the two are written in one place, which is the helper's");
        assertNotEquals(held.get(0).which(), held.get(1).which(),
                "and are two occurrences all the same, each reached under its own conditions");
    }

    /**
     * Two modules that name a behavior alike name their comparisons apart.
     *
     * <p>What a name has to do. A behavior's name is one module's word, so a name made of that and
     * a number tells two modules' first comparisons apart nowhere — and the node this replaced was
     * distinct across everything there is, being an object. A reading of one module would join to
     * the other module's comparison and answer about it.
     */
    @Test
    void twoModulesNamingABehaviorAlikeNameTheirComparisonsApart() {
        String body = """
                module %s

                behavior check : (a: Int) -> Int

                let check (a) = if a > 10 then 1 else 2
                """;
        ComparisonCatalog here =
                ComparisonCatalog.of(new ModuleBodies("one", bodiesOf(body.formatted("one"))));
        ComparisonCatalog there =
                ComparisonCatalog.of(new ModuleBodies("two", bodiesOf(body.formatted("two"))));

        assertEquals(1, here.all().size(), "each module writes one comparison");
        assertEquals(1, there.all().size(), "each module writes one comparison");
        assertNotEquals(here.all().get(0).which(), there.all().get(0).which(),
                "and the two are not one comparison");
    }

    /**
     * A plan is not about another module's comparison, and says so.
     *
     * <p>Refused rather than answered. A comparison this plan numbers no site for and one belonging
     * to another module both have no site, and a plan that answered alike would let a reading of
     * one module ask about the other's and take "nothing records a run through it" for an answer
     * about its own.
     */
    @Test
    void aPlanRefusesAComparisonOfAnotherModule() {
        String body = """
                module %s

                behavior check : (a: Int) -> Int

                let check (a) = if a > 10 then 1 else 2
                """;
        CoverageSites.Plan here = CoverageSites.of(
                new ModuleBodies("one", bodiesOf(body.formatted("one"))),
                DecisionSources.NONE, SuppliedRules.NONE);
        ComparisonOccurrence there = ComparisonCatalog.of(
                new ModuleBodies("two", bodiesOf(body.formatted("two")))).all().get(0).which();

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> here.instruments(there));
        assertTrue(refused.getMessage().contains("not about"), refused.getMessage());
    }

    /** Every binary of {@code e} the language reads as a comparison, in the order it is written. */
    private static void recognised(Core e, java.util.function.Consumer<Core.Binary> each) {
        if (e instanceof Core.Binary binary
                && souther.compiler.check.Comparison.of(binary).isPresent()) {
            each.accept(binary);
        }
        Core.forEachChild(e, child -> recognised(child, each));
    }

    /** What the catalog holds is what the plan numbers, wherever the comparison stands. */
    @Test
    void aComparisonGivenANameBeforeTheForkIsNumbered() {
        CoverageSites.Plan plan = planOf(bodiesOf(NAMED_BEFORE_THE_FORK));

        assertEquals(1, plan.sites().stream()
                        .filter(site -> site.outcome() instanceof SourceOutcome.Compared)
                        .count(),
                "the comparison the name stands for is numbered: " + plan.sites());
    }
}
