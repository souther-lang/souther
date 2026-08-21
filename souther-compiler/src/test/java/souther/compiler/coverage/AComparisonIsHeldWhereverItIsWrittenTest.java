package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
        ComparisonCatalog catalog = ComparisonCatalog.of(bodiesOf(source));
        return catalog.comparisons().stream().map(each -> each.node().op().name()).toList();
    }

    private static final String NAMED_BEFORE_THE_FORK = """
            module example.named

            behavior fee : (a: Int) -> Int

            let fee (a) = {
                let ok = a > 1

                if ok then 1 else 0
            }
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
        assertEquals(List.of("GT"), operatorsIn("""
                module example.inside

                behavior positives : (xs: List<Int>) -> List<Int>

                let positives (xs) = List.filter(x -> x > 0, xs)
                """));
    }

    /**
     * A plan that numbered something other than a comparison is refused where it is built.
     *
     * <p>What the emitter does with a number is copy the value the node left on the stack, so a
     * number on {@code a + b} hands it half a {@code long} to copy and the class will not verify.
     * Said here rather than left to the emitter, because the emitter is the last reader and a plan
     * is what every earlier one joins on: a numbering that got this wrong would have been agreed
     * with by the reading, the partition and the reachability before anything ran.
     */
    @Test
    void aPlanCannotNumberSomethingThatIsNotAComparison() {
        Core.Binary sum = (Core.Binary) sumIn("""
                module example.sum

                behavior total : (a: Int, b: Int) -> Int

                let total (a, b) = a + b
                """);
        IdentityHashMap<Core, Integer> numbered = new IdentityHashMap<>();
        numbered.put(sum, 0);

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new CoverageSites.Plan(List.of(), List.of(), new IdentityHashMap<>(),
                        numbered));
        assertTrue(refused.getMessage().contains("ADD"), refused.getMessage());
    }

    private static Core sumIn(String source) {
        Core body = bodiesOf(source).get("total");
        while (!(body instanceof Core.Binary)) {
            body = switch (body) {
                case Core.LetIn let -> let.body();
                case Core.Block block -> block.body();
                default -> throw new AssertionError("no binary in this body: " + body);
            };
        }
        return body;
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
        CoverageSites.Plan plan = CoverageSites.of(bodies);
        Core.Binary comparison = ComparisonCatalog.of(bodies).comparisons().get(0).node();

        assertTrue(plan.comparisonAt(comparison).isPresent(), "it is numbered");
        assertTrue(plan.mayRepeat(comparison), "and one run may pass it once per element");
    }

    /** What the catalog holds is what the plan numbers, wherever the comparison stands. */
    @Test
    void aComparisonGivenANameBeforeTheForkIsNumbered() {
        CoverageSites.Plan plan = CoverageSites.of(bodiesOf(NAMED_BEFORE_THE_FORK));

        assertEquals(1, plan.sites().stream()
                        .filter(site -> site.outcome() instanceof SourceOutcome.Compared)
                        .count(),
                "the comparison the name stands for is numbered: " + plan.sites());
    }
}
