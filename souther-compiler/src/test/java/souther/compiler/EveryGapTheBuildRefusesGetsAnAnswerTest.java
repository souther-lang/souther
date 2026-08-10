package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.GenerationOutcome;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a build refuses, the generator answers — with a row, or with why there is none.
 *
 * <p>A generator that offers rows for the gaps it has a strategy for and says nothing about the rest
 * reads as though the block filled everything. An author who takes every row it offers is left with a
 * model that still fails, and nothing told them which part of the shortfall was never attempted.
 *
 * <p>So the answer is total over the findings a build refuses. Which of the three it is depends on
 * whether a strategy applies, not on what a search happened to do: a strategy that recognised the gap
 * and composed nothing is not the same as no strategy for the gap at all.
 */
class EveryGapTheBuildRefusesGetsAnAnswerTest {

    /** Two boundary gaps a strategy composes a row for, and an arm no strategy reaches. */
    private static final String POLICY = """
            module example.policy

            data Rate = Int
                invariant nonNegative = value >= 0

            data Cap = Int
                invariant nonNegative = value >= 0

            data Policy =
                { rate: Rate
                , cap: Cap
                }

            behavior fee : (days: Int, policy: Policy) -> Int

            let fee (days, policy) = {
                let accrued = days * policy.rate.value

                if accrued > policy.cap.value then policy.cap.value else accrued
            }

            example fee
                | "under the cap" : (5, Policy { rate = Rate(10), cap = Cap(500) }) -> 50
            """;

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    private static List<Adequacy.Finding> gaps(Compilation compilation, String module,
                                               String behavior) {
        Map<String, List<Adequacy.Finding>> found =
                compilation.db().ask(new Adequacy.Findings(module)).value();
        assertNotNull(found, "the model under test compiles");
        return found.get(behavior).stream().filter(Adequacy.Finding::isAdequacyGap).toList();
    }

    private static Adequacy.Filling filling(Compilation compilation, String module,
                                            String behavior) {
        Map<String, Adequacy.Filling> generated =
                compilation.db().ask(new Adequacy.Generated(module)).value();
        assertNotNull(generated, "the model under test compiles");
        return generated.get(behavior);
    }

    @Test
    void everyGapTheBuildRefusesHasOneAnswer() {
        Compilation compilation = compiled(POLICY);
        List<Adequacy.Finding> gaps = gaps(compilation, "example.policy", "fee");

        assertFalse(gaps.isEmpty(), "the model under test has gaps to answer for");
        assertEquals(gaps,
                filling(compilation, "example.policy", "fee").gaps().stream()
                        .map(Adequacy.GapDisposition::gap).toList(),
                "one answer per gap, in the order the findings were established");
    }

    @Test
    void aBoundaryARowWasComposedForIsAnsweredWithThatRow() {
        Compilation compilation = compiled(POLICY);
        List<Adequacy.GapDisposition> answered =
                filling(compilation, "example.policy", "fee").gaps().stream()
                        .filter(d -> d.gap().kind() == Adequacy.Kind.BOUNDARY_UNMET).toList();

        assertEquals(2, answered.size(), "both edges");
        assertTrue(answered.stream().allMatch(
                        d -> d.outcome() instanceof GenerationOutcome.Generated),
                "a strategy applies to a boundary and it composed a row: " + answered);
    }

    @Test
    void anArmNoStrategyReachesIsNotSupportedRatherThanUnanswered() {
        Compilation compilation = compiled(POLICY);
        List<Adequacy.GapDisposition> arms =
                filling(compilation, "example.policy", "fee").gaps().stream()
                        .filter(d -> d.gap().kind() == Adequacy.Kind.ARM_UNREACHED).toList();

        assertEquals(1, arms.size());
        assertTrue(arms.get(0).outcome()
                        instanceof GenerationOutcome.NotSupported,
                "no strategy composes an input to reach an arm: " + arms);
    }

    // --- a case of an input, which is the one gap the three answers all reach ---------------------

    /** A sum of unit cases, one of which no row applies the behavior to. */
    private static final String KIND = """
            module example.kind

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas

            data Fine
            data Broke
            data Verdict = Fine | Broke

            behavior pick : (k: Kind) -> Verdict

            let pick (k) = match k with
                | Domestic -> Fine
                | Overseas -> Fine

            example pick
                | "home" : (Domestic) -> Fine
            """;

    /** The same, with a case that carries a field whose value nothing here composes. */
    private static final String CARRIED = """
            module example.pay

            data Amount = Decimal
                invariant value >= 0.0m

            data Card = { holder: Amount }
            data Cash = { amount: Amount }
            data Payment = Card | Cash

            data Fine
            data Broke
            data Verdict = Fine | Broke

            behavior feeFor : (p: Payment) -> Verdict

            let feeFor (p) = match p with
                | Card -> Fine
                | Cash -> Fine

            example feeFor
                | "cash" : (Cash { amount = Amount(0.0m) }) -> Fine
            """;

    /** More divided positions than the partition keeps axes for, so the last ones have none. */
    private static final String WIDE = wide(13);

    private static String wide(int positions) {
        StringBuilder names = new StringBuilder();
        StringBuilder declared = new StringBuilder();
        StringBuilder written = new StringBuilder();
        for (int at = 1; at <= positions; at++) {
            names.append(at == 1 ? "" : ", ").append("k").append(at);
            declared.append(at == 1 ? "" : ", ").append("k").append(at).append(": Kind");
            written.append(at == 1 ? "" : ", ").append("Domestic");
        }
        return """
                module example.wide

                data Domestic
                data Overseas
                data Kind = Domestic | Overseas

                data Fine
                data Broke
                data Verdict = Fine | Broke

                behavior pick : (%s) -> Verdict

                let pick (%s) = Fine

                example pick
                    | "all home" : (%s) -> Fine
                """.formatted(declared, names, written);
    }

    /** The answer for the case named {@code missing} of the input at {@code at}, one-based. */
    private static GenerationOutcome forCase(Compilation compilation, String module,
                                             String behavior, String missing, int at) {
        return filling(compilation, module, behavior).gaps().stream()
                .filter(each -> each.gap().kind() == Adequacy.Kind.INPUT_CASE_UNSPECIFIED)
                .filter(each -> each.gap().args().get(0).equals(missing)
                        && ((Number) each.gap().args().get(1)).intValue() == at)
                .map(Adequacy.GapDisposition::outcome)
                .findFirst().orElseThrow(() -> new AssertionError("no gap for " + missing));
    }

    @Test
    void aCaseAnAxisDividesAndAValueComposesForIsAnsweredWithARow() {
        GenerationOutcome answer = forCase(compiled(KIND), "example.kind", "pick", "Overseas", 1);

        assertInstanceOf(GenerationOutcome.Generated.class, answer);
        assertEquals(List.of("Overseas"),
                ((GenerationOutcome.Generated) answer).candidates().stream()
                        .map(row -> row.inputs().get(0).text()).toList());
    }

    /**
     * A case an axis divides and nothing composed a value for is answered by the attempt.
     *
     * <p>Not {@code NotSupported}: the strategy took this class and came back with a reason, which is
     * news of a different kind. What it came back with here is a refusal a hand-written row would
     * settle, and reading it as "no strategy for this" would say the generator will never offer one.
     */
    @Test
    void aCaseNothingComposedAValueForIsAnsweredByTheAttempt() {
        GenerationOutcome answer = forCase(compiled(CARRIED), "example.pay", "feeFor", "Card", 1);

        assertInstanceOf(GenerationOutcome.CannotGenerate.class, answer);
    }

    /**
     * A case at a position no axis was derived at is one nothing takes.
     *
     * <p>Read off the axes rather than off an empty row list. A search that wrote no row at this class
     * and a partition that never divided the position leave the same absence behind, and only the
     * second of them is a fact about what the generator can do.
     */
    @Test
    void aCaseAtAPositionNoAxisWasDerivedAtIsNotSupported() {
        Compilation compilation = compiled(WIDE);

        assertInstanceOf(GenerationOutcome.Generated.class,
                forCase(compilation, "example.wide", "pick", "Overseas", 1),
                "a position inside the axis limit is divided and offered");
        assertEquals(new GenerationOutcome.NotSupported(
                        GenerationOutcome.NotSupported.Reason.NO_AXIS_AT_THIS_POSITION),
                forCase(compilation, "example.wide", "pick", "Overseas", 13),
                "and one past it is not something anything here takes");
    }

    @Test
    void aCaseOfTheOutputIsNotSupported() {
        List<GenerationOutcome> outputs = filling(compiled(KIND), "example.kind", "pick").gaps()
                .stream()
                .filter(each -> each.gap().kind() == Adequacy.Kind.OUTPUT_CASE_UNSPECIFIED)
                .map(Adequacy.GapDisposition::outcome).toList();

        assertEquals(List.of(new GenerationOutcome.NotSupported(
                        GenerationOutcome.NotSupported.Reason.NO_STRATEGY_FOR_AN_OUTPUT_CASE)),
                outputs, "nothing searches for an input by the case it would answer with");
    }

    // --- classes that were not there, and classes that would not link -----------------------------

    private static String saidAbout(souther.compiler.partition.GenerationReason why,
                                    souther.compiler.partition.GenerationReason alsoAtTheEdges) {
        return GeneratedRows.of("example.kind",
                Map.of("pick", new Adequacy.Filling(stopped(why), stopped(alsoAtTheEdges),
                        List.of())),
                true);
    }

    private static souther.compiler.partition.Generator.GenerationResult stopped(
            souther.compiler.partition.GenerationReason why) {
        return why == null ? souther.compiler.partition.Generator.GenerationResult.NONE
                : new souther.compiler.partition.Generator.GenerationResult(
                        List.of(), List.of(), List.of(why));
    }

    /**
     * Classes that would not link are not classes that were not there.
     *
     * <p>The assessment records which of the two it met, and both leave no row to offer. That is all
     * they share: a sentence saying the classes were not there, printed where they were built and
     * could not be reached, is this compiler choosing which of the things it saw to report.
     */
    @Test
    void classesThatWouldNotLinkAreNotClassesThatWereNotThere() {
        String linked = saidAbout(
                new souther.compiler.partition.GenerationReason.LinkageFailed("pick"), null);
        String absent = saidAbout(
                new souther.compiler.partition.GenerationReason.NothingToBuildAgainst("pick"), null);

        assertFalse(linked.isBlank(), "the one it met is said");
        assertFalse(absent.isBlank(), "and so is the other");
        assertNotEquals(absent, linked,
                "two reasons reported in one sentence are one reason:\n" + linked);
    }

    /**
     * One reason both searches stopped for is said once.
     *
     * <p>Nothing to put a candidate through stops the pair search and the edges alike, and the two
     * results carry it separately. Printed from each, a reader is told twice that generation stopped
     * and reads two things having gone wrong.
     */
    @Test
    void oneReasonBothSearchesStoppedForIsSaidOnce() {
        souther.compiler.partition.GenerationReason why =
                new souther.compiler.partition.GenerationReason.LinkageFailed("pick");

        assertEquals(saidAbout(why, null), saidAbout(why, why),
                "the second search stopping for the reason the first did adds nothing to say");
    }

    @Test
    void anArmNoStrategyReachesIsNamedInTheBlock() {
        Compilation compilation = compiled(POLICY);
        Map<String, Adequacy.Filling> generated =
                compilation.db().ask(new Adequacy.Generated("example.policy")).value();
        String block = GeneratedRows.of("example.policy", generated, true);

        assertTrue(block.contains("`then`"),
                "the arm nothing offers a row for is named: " + block);
    }
}
