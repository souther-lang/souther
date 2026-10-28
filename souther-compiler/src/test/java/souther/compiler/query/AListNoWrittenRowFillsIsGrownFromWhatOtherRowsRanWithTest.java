package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.partition.Replacement;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A list the written rows ran with empty is grown by one element the rows of another behavior ran
 * with, and which element is tried does not turn on what else the module declares or on what else
 * the rows hold.
 *
 * <p>The element that tells a rewrite apart is one value among those the module's rows ran with;
 * what keeps it from being tried is anything standing before it in the search: a behavior named
 * earlier, values of the same type that tell nothing, numbers elsewhere in the same row that the
 * search moves first.
 */
class AListNoWrittenRowFillsIsGrownFromWhatOtherRowsRanWithTest {

    private static final String TAGS = """
            module repro.tags

            data Tag = Int
                invariant value >= 0 && value <= 100

            behavior weight : (t: Tag) -> Int

            let weight (t) = if t.value > 50 then 1 else 0

            example weight
                | (Tag(10)) -> 0
                | (Tag(60)) -> 1

            %s

            behavior score : (tags: List<Tag>) -> Int

            let score (tags) = List.fold((acc, t) -> acc + weight(t), 0, tags)

            example score
                | ([]) -> 0
            """;

    /** Eight values of the type that weigh nothing, in a behavior whose name sorts before the one
     *  that holds the value that does. */
    private static final String SAMPLES = """
            behavior aSamples : (t: Tag) -> Int

            let aSamples (t) = 0

            example aSamples
                | (Tag(11)) -> 0
                | (Tag(12)) -> 0
                | (Tag(13)) -> 0
                | (Tag(14)) -> 0
                | (Tag(15)) -> 0
                | (Tag(16)) -> 0
                | (Tag(17)) -> 0
                | (Tag(18)) -> 0
                | (Tag(19)) -> 0
                | (Tag(20)) -> 0
            """;

    @Test
    void theElementThatTellsIsTriedWhateverElseTheModuleDeclares() {
        assertToldApart(TAGS.formatted(""));
        assertToldApart(TAGS.formatted(SAMPLES));
        assertToldApart(TAGS.formatted(SAMPLES.replace("aSamples", "zSamples")));
    }

    /** Numbers in the same row are moved by one first, and there are many of them. */
    @Test
    void theElementThatTellsIsTriedWhereTheRowAlsoHoldsManyNumbers() {
        String numbers = """
                module repro.numbers

                data Tag = Int
                    invariant value >= 0 && value <= 100

                behavior weight : (t: Tag) -> Int

                let weight (t) = if t.value > 50 then 1 else 0

                example weight
                    | (Tag(10)) -> 0
                    | (Tag(60)) -> 1

                behavior score : (tags: List<Tag>, noise: List<Int>) -> Int

                let score (tags, noise) = List.fold((acc, t) -> acc + weight(t), 0, tags)

                example score
                    | ([], [%s]) -> 0
                """.formatted(java.util.stream.IntStream.range(0, 60)
                .mapToObj(Integer::toString).collect(java.util.stream.Collectors.joining(", ")));

        assertToldApart(numbers);
    }

    /** The same hole in the search for an arm: the one row goes through the arm with no element,
     *  and the fork turns on what another behavior answers for the elements. */
    @Test
    void anArmTheRowsReachWithAnEmptyListIsToldApartByAGrownList() {
        String source = """
                module repro.arm

                data Tag = Int
                    invariant value >= 0 && value <= 100

                behavior weight : (t: Tag) -> Int

                let weight (t) = if t.value > 50 then 1 else 0

                example weight
                    | (Tag(10)) -> 0
                    | (Tag(60)) -> 1

                behavior score : (tags: List<Tag>) -> Int

                let score (tags) = {
                    let total = List.fold((acc, t) -> acc + weight(t), 0, tags)
                    if total > 0 then total else List.length(tags) * 3
                }

                example score
                    | ([]) -> 0
                """;

        Map<Replacement, ReplacementEvidence.Outcome> rewrites = rewritesOf(source, "score");

        assertEquals(List.of(), rewrites.values().stream()
                        .filter(each -> !(each instanceof ReplacementEvidence.Unnoticed))
                        .toList(),
                () -> "every rewrite of the arm the row reaches is shown to differ: " + rewrites);
    }

    private static void assertToldApart(String source) {
        List<ReplacementEvidence.Outcome> oneAnswer = oneAnswers(rewritesOf(source, "score"));

        assertEquals(1, oneAnswer.size(), () -> "a rewrite for the one value: " + oneAnswer);
        assertInstanceOf(ReplacementEvidence.Unnoticed.class, oneAnswer.getFirst(),
                () -> "a list of the tag that weighs answers otherwise than the constant: "
                        + oneAnswer);
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

    private static Map<Replacement, ReplacementEvidence.Outcome> rewritesOf(String source,
                                                                            String behavior) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code()).toList(),
                "the model under test compiles");
        String module = compilation.modules().get(0);
        ReplacementEvidence its =
                compilation.db().ask(new Replacements.Measured(module)).value().get(behavior);
        Map<Replacement, ReplacementEvidence.Outcome> out = new LinkedHashMap<>();
        its.measured().made().orElseThrow(() -> new AssertionError(
                        "the rewrites were measured: " + its.measured()))
                .rewrites().forEach(each -> out.put(each.replacement(), each.outcome()));
        return out;
    }
}
