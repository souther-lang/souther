package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;
import souther.compiler.partition.Replacement;
import souther.compiler.regex.PatternPlan;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a search for a row a rewrite is told by looks first, and how the ways it looks share what
 * it may spend.
 *
 * <p>The values a list is grown from are the rows of the behaviors the subject calls before the
 * rows of the module, so a behavior the subject has nothing to do with, declared before or after,
 * does not stand ahead of the value that tells the rewrite apart however few runs there are. The
 * ways of looking put a candidate each in turn, so the arm search that finds a row by moving a
 * position of one a run went through is not left without runs by a list that has many values to
 * be grown with. And a candidate made and refused costs something too, and a search that stops
 * making them says so.
 */
class TheWaysOfLookingForARowShareOneBudgetAndStartFromWhatTheSubjectCallsTest {

    private static final String TAG = """
            data Tag = Int
                invariant value >= 0 && value <= 100
            """;

    private static final String WEIGHT = """
            behavior weight : (t: Tag) -> Int

            let weight (t) = if t.value > 50 then 1 else 0

            example weight
                | (Tag(10)) -> 0
                | (Tag(60)) -> 1
            """;

    /** A behavior of the module the subject has nothing to do with, with rows of the same type
     *  that tell nothing, and values no other such behavior has. */
    private static String unrelated(String name, int first) {
        return """
                behavior %1$s : (t: Tag) -> Int

                let %1$s (t) = 0

                example %1$s
                    | (Tag(%2$d)) -> 0
                    | (Tag(%3$d)) -> 0
                    | (Tag(%4$d)) -> 0
                """.formatted(name, first, first + 1, first + 2);
    }

    private static final String SCORE = """
            behavior score : (tags: List<Tag>) -> Int

            let score (tags) = List.fold((acc, t) -> acc + weight(t), 0, tags)

            example score
                | ([]) -> 0
            """;

    @Test
    void theRowsOfWhatTheSubjectCallsComeBeforeThoseOfBehaviorsItHasNothingToDoWith() {
        String before = IntStream.range(0, 8).mapToObj(each -> unrelated("a" + each, 11 + 3 * each))
                .collect(Collectors.joining("\n"));
        String after = IntStream.range(0, 8).mapToObj(each -> unrelated("z" + each, 11 + 3 * each))
                .collect(Collectors.joining("\n"));

        for (String source : List.of(
                "module repro.called\n\n" + TAG + "\n" + before + "\n" + WEIGHT + "\n" + SCORE,
                "module repro.called\n\n" + TAG + "\n" + WEIGHT + "\n" + after + "\n" + SCORE)) {
            Map<Replacement, ReplacementEvidence.Outcome> rewrites =
                    rewritesOf(compiled(List.of(source), 6), "repro.called", "score");

            ReplacementEvidence.Outcome only = oneAnswers(rewrites).getFirst();
            assertInstanceOf(ReplacementEvidence.Unnoticed.class, only,
                    () -> "the tag that weighs is the first one tried: " + only);
        }
    }

    @Test
    void aBehaviorOfAnotherModuleTheSubjectCallsIsFollowedToItsRows() {
        String weights = "module repro.weights\n\n" + TAG + "\n" + WEIGHT;
        String scoring = "module repro.scoring\n\nimport repro.weights ( Tag, weight )\n\n" + SCORE;

        Map<Replacement, ReplacementEvidence.Outcome> rewrites = rewritesOf(
                compiled(List.of(weights, scoring), 6), "repro.scoring", "score");

        ReplacementEvidence.Outcome only = oneAnswers(rewrites).getFirst();
        assertInstanceOf(ReplacementEvidence.Unnoticed.class, only,
                () -> "the rows of the module it imports are the ones it is handed: " + only);
    }

    /**
     * An arm the rows go through is told by moving one position of the row, since a relation
     * between two numbers is no side of a class. A list with many values to be grown with is a way
     * of looking too, and does not leave this none of the runs.
     */
    @Test
    void aListWithManyValuesToGrowItWithDoesNotLeaveTheMovingOfAPositionNoRuns() {
        String seeds = IntStream.range(0, 12).mapToObj(each -> "    | (Tag(" + (11 + each)
                        + ")) -> 0").collect(Collectors.joining("\n"));
        String source = """
                module repro.moving

                %s

                behavior sample : (t: Tag) -> Int

                let sample (t) = 0

                example sample
                %s

                behavior pick : (a: Int, b: Int, tags: List<Tag>) -> Int

                let pick (a, b, tags) = if a > b then a - b else 0

                example pick
                    | (1, 1, []) -> 0
                """.formatted(TAG, seeds);

        Map<Replacement, ReplacementEvidence.Outcome> rewrites =
                rewritesOf(compiled(List.of(source), 6), "repro.moving", "pick");

        List<ReplacementEvidence.Outcome> arms = new ArrayList<>();
        rewrites.forEach((rewrite, outcome) -> {
            if (rewrite instanceof Replacement.OfAnArm) {
                arms.add(outcome);
            }
        });
        assertEquals(List.of(ReplacementEvidence.Unnoticed.class),
                arms.stream().map(Object::getClass).distinct().toList(),
                () -> "every arm the row goes through is shown to differ: " + rewrites);
    }

    /**
     * Candidates the position's own rules refuse are made all the same, and a search that stops
     * making them says it did, at the figure a walk composing rows is held to.
     */
    @Test
    void candidatesMadeAndRefusedAreCountedAndTheStopIsSaid() {
        String seeds = IntStream.range(0, 80).mapToObj(each -> "    | (Tag(" + each
                        + ")) -> 0").collect(Collectors.joining("\n"));
        String source = """
                module repro.refused

                %s

                data Bag = List<Tag>
                    invariant List.length(value) <= 0

                behavior sample : (t: Tag) -> Int

                let sample (t) = 0

                example sample
                %s

                behavior size : (b: Bag) -> Int

                let size (b) = List.length(b.value) * 0

                example size
                    | (Bag([])) -> 0
                """.formatted(TAG, seeds);

        Map<Replacement, ReplacementEvidence.Outcome> rewrites =
                rewritesOf(compiled(List.of(source), Budgets.measures().rewriteRuns()),
                        "repro.refused", "size");

        ReplacementEvidence.Undecided open = assertInstanceOf(ReplacementEvidence.Undecided.class,
                oneAnswers(rewrites).getFirst(), () -> "left open: " + rewrites);
        assertTrue(open.why().ways().stream().anyMatch(way ->
                        way.why() == ReplacementEvidence.Undecided.Why.A_COMPOSING_FIGURE_REACHED
                                && way.figures().contains(
                                WorkFigure.CANDIDATES_A_REPAIR_BUILDS.at(64))),
                () -> "stopped at the figure, and not found absent: " + open);
    }

    private static List<ReplacementEvidence.Outcome> oneAnswers(
            Map<Replacement, ReplacementEvidence.Outcome> rewrites) {
        List<ReplacementEvidence.Outcome> out = new ArrayList<>();
        rewrites.forEach((rewrite, outcome) -> {
            if (rewrite instanceof Replacement.ByOneAnswer) {
                out.add(outcome);
            }
        });
        return out;
    }

    private static Map<Replacement, ReplacementEvidence.Outcome> rewritesOf(
            Compilation compilation, String module, String behavior) {
        ReplacementEvidence its =
                compilation.db().ask(new Replacements.Measured(module)).value().get(behavior);
        Map<Replacement, ReplacementEvidence.Outcome> out = new LinkedHashMap<>();
        its.measured().made().orElseThrow(() -> new AssertionError(
                        "the rewrites were measured: " + its.measured()))
                .rewrites().forEach(each -> out.put(each.replacement(), each.outcome()));
        return out;
    }

    private static Compilation compiled(List<String> sources, int rewriteRuns) {
        Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY)
                .withAdequacyPolicy(new AdequacyPolicy(
                        new AdequacyPolicy.OfTheMeasures(Budgets.measures().pairSpace(),
                                Budgets.measures().cellsPerGroup(),
                                PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS, rewriteRuns),
                        Budgets.generation()));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
