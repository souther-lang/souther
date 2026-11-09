package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row a rewrite is told apart on is looked for among the values the body answers differently at,
 * and a parameter the body never reads is none of them: every value of it answers as the origin's
 * does. So how many such parameters a behavior has, and whether they are declared before or after
 * the one that decides, does not change whether the rewrite is told apart within what a search may
 * run.
 *
 * <p>The body below answers false at the row written and true at a value of {@code x} above a
 * thousand, and every run counts. Each flag moved before {@code x} is a run that tells nothing.
 */
class AParameterTheBodyDoesNotReadSpendsNoneOfWhatARewriteIsLookedForWithTest {

    private static final int RUNS = 6;

    private static String behaviorWith(int flags, boolean flagsFirst) {
        String declared = IntStream.range(0, flags).mapToObj(each -> "f" + each + ": Flag")
                .collect(Collectors.joining(", "));
        String names = IntStream.range(0, flags).mapToObj(each -> "f" + each)
                .collect(Collectors.joining(", "));
        String row = IntStream.range(0, flags).mapToObj(each -> "On")
                .collect(Collectors.joining(", "));
        String sep = flags == 0 ? "" : ", ";
        return """
                module example.runs

                data Ok = { big: Bool }
                data On
                data Off
                data Flag = On | Off

                behavior f : (%s) -> Ok
                    constructs Ok

                let f (%s) = Ok { big = x > 1000 }

                example f
                    | (%s) -> Ok { big = false }
                """.formatted(
                flagsFirst ? declared + sep + "x: Int" : "x: Int" + sep + declared,
                flagsFirst ? names + sep + "x" : "x" + sep + names,
                flagsFirst ? row + sep + "5" : "5" + sep + row);
    }

    private static List<ReplacementEvidence.Outcome> outcomesOfTheAnswers(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY)
                .withAdequacyPolicy(new AdequacyPolicy(
                        new AdequacyPolicy.OfTheMeasures(Budgets.measures().pairSpace(),
                                Budgets.measures().cellsPerGroup(),
                                PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS, RUNS),
                        Budgets.generation()));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code()).toList(),
                "the model under test compiles");
        ReplacementEvidence its = compilation.db()
                .ask(new Replacements.Measured("example.runs")).value().get("f");
        Map<Replacement, ReplacementEvidence.Outcome> rewrites = new LinkedHashMap<>();
        its.measured().made().orElseThrow().rewrites()
                .forEach(each -> rewrites.put(each.replacement(), each.outcome()));
        List<ReplacementEvidence.Outcome> answers = new ArrayList<>();
        rewrites.forEach((rewrite, outcome) -> {
            if (rewrite instanceof Replacement.ByOneAnswer) {
                answers.add(outcome);
            }
        });
        return answers;
    }

    /**
     * Only the parameters the body never reads stand. The row that tells the rewrite apart moves
     * two parameters the body does read, at once, and is found beside flags that stand.
     */
    @Test
    void parametersTheBodyReadsAreStillMovedTogetherBesideFlagsThatStand() {
        for (int count : new int[] {0, 4}) {
            assertToldApartBesideFlags(count);
        }
    }

    private static void assertToldApartBesideFlags(int count) {
        String flags = IntStream.range(0, count).mapToObj(each -> "f" + each + ": Flag, ")
                .collect(Collectors.joining());
        String names = IntStream.range(0, count).mapToObj(each -> "f" + each + ", ")
                .collect(Collectors.joining());
        String row = IntStream.range(0, count).mapToObj(each -> "On, ")
                .collect(Collectors.joining());
        String source = """
                module example.runs

                data Ok = { big: Bool }
                data On
                data Off
                data Flag = On | Off

                behavior f : (%sx: Int, y: Int) -> Ok
                    constructs Ok

                let f (%sx, y) = Ok { big = x > 1000 && y > 1000 }

                example f
                    | (%s5, 5) -> Ok { big = false }
                """.formatted(flags, names, row);

        List<ReplacementEvidence.Outcome> answers = outcomesOfTheAnswers(source);

        assertTrue(!answers.isEmpty(), "the body answering one value is a rewrite");
        assertEquals(List.of(ReplacementEvidence.Unnoticed.class),
                answers.stream().map(Object::getClass).distinct().toList(),
                () -> count + " flags: " + answers);
    }

    @Test
    void flagsTheBodyDoesNotReadDoNotUseUpTheRunsInFrontOfTheOneThatDecides() {
        for (boolean flagsFirst : new boolean[] {true, false}) {
            for (int flags : new int[] {0, 4, 8}) {
                List<ReplacementEvidence.Outcome> answers =
                        outcomesOfTheAnswers(behaviorWith(flags, flagsFirst));

                assertTrue(!answers.isEmpty(), "the body answering one value is a rewrite");
                assertEquals(List.of(ReplacementEvidence.Unnoticed.class),
                        answers.stream().map(Object::getClass).distinct().toList(),
                        () -> flags + " flags " + (flagsFirst ? "before" : "after")
                                + " the number: " + answers);
            }
        }
    }
}
