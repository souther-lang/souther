package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
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
 * Every finding gets one generation disposition, and which bar a build asked for is no part of it.
 *
 * <p>A generator that offers rows for the findings it has a strategy for and says nothing about the
 * rest reads as though the block filled everything. An author who takes every row it offers is left
 * with a model that still fails, and nothing told them which part of the shortfall was never
 * attempted.
 *
 * <p>So the answer is total over the findings — <em>all</em> of them. It used to be total over the
 * ones a build refuses over, which is the coupling this holds against: what a bar refuses and what
 * a search can compose are two projections of one set of findings, and the first was standing in
 * the doorway of the second. A finding no bar had been asked for went unanswered, and no strategy
 * could be written for one until some bar gated on it first.
 *
 * <p>Which of the four it is depends on whether a strategy applies, not on what a search happened
 * to do: a strategy that recognised the finding and composed nothing is not the same as no strategy
 * for it at all, and neither is the same as a finding no row would answer.
 *
 * <p><b>Beside the exhaustive switch and not instead of it.</b> The compiler makes somebody answer
 * for a new shape of finding; this makes sure nothing filters one out before the switch is reached.
 * That is exactly what went wrong — a class no row is in was listed in the switch and dropped by
 * the line above it.
 */
class EveryFindingHasAGenerationDispositionTest {

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
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /**
     * Every finding of one behavior, filtered by nothing.
     *
     * <p>No filter, and that is the point rather than a simplification. Narrowing to what some bar
     * refuses over is what this exists to refuse: the two lists compared below would then be
     * answers to one question asked twice, and would agree however much was being dropped between
     * the findings and the dispositions.
     */
    private static List<Adequacy.Finding> findings(Compilation compilation, String module,
                                                   String behavior) {
        Map<String, List<Adequacy.Finding>> found =
                compilation.db().ask(new Adequacy.Findings(module)).value();
        assertNotNull(found, "the model under test compiles");
        return found.get(behavior);
    }

    private static Adequacy.Filling filling(Compilation compilation, String module,
                                            String behavior) {
        Map<String, Adequacy.Filling> generated =
                compilation.db().ask(new Adequacy.Generated(module)).value();
        assertNotNull(generated, "the model under test compiles");
        return generated.get(behavior);
    }

    @Test
    void everyFindingHasOneAnswer() {
        Compilation compilation = compiled(POLICY);
        List<Adequacy.Finding> findings = findings(compilation, "example.policy", "fee");

        assertFalse(findings.isEmpty(), "the model under test has findings to answer for");
        assertEquals(findings,
                filling(compilation, "example.policy", "fee").generation().stream()
                        .map(Adequacy.GenerationDisposition::finding).toList(),
                "one answer per finding, in the order the findings were established");
    }

    /**
     * And the same list whichever bar the run was held to.
     *
     * <p>The other half of the separation. The list above could be total over the findings and
     * still be decided by the bar — a stricter one having more of them — and what says it is not is
     * that two runs of one model under two bars answer for the same findings.
     */
    @Test
    void whatIsAnsweredForDoesNotMoveWithTheBar() {
        for (Adequacy.AdequacyBar bar : Adequacy.AdequacyBar.values()) {
            Compilation compilation = Compilation.ofSource(POLICY, "Main");
            compilation.measure(Adequacy.Asked.fullReport(bar));
            compilation.answerEverything();

            // Held within one compilation, because that is where the two lists are the same
            // findings. Compared across two, a border's finding carries the region its row was
            // composed over, which is one object per run and equal to nothing else — so the
            // comparison would be about object identity rather than about what was answered for.
            List<Adequacy.Finding> found = findings(compilation, "example.policy", "fee");
            assertFalse(found.isEmpty(), "the model under test has findings to answer for");
            assertEquals(found,
                    filling(compilation, "example.policy", "fee").generation().stream()
                            .map(Adequacy.GenerationDisposition::finding).toList(),
                    bar::name);
        }
    }

    @Test
    void aBoundaryARowWasComposedForIsAnsweredWithThatRow() {
        Compilation compilation = compiled(POLICY);
        List<Adequacy.GenerationDisposition> answered =
                filling(compilation, "example.policy", "fee").generation().stream()
                        .filter(d -> d.finding().kind() == Adequacy.Kind.BOUNDARY_UNMET).toList();

        assertEquals(2, answered.size(), "both edges");
        assertTrue(answered.stream().allMatch(
                        d -> d.outcome() instanceof GenerationOutcome.Generated),
                "a strategy applies to a boundary and it composed a row: " + answered);
    }

    /** A body whose decisions read two positions together, so the combinations reach its arms. */
    private static final String SHIPPING = """
            module example.shipping

            data Membership = Premium | Standard
            data Delivery = Express | Regular

            data Fee = Int
                invariant value >= 0

            behavior shippingFee : (member: Membership, delivery: Delivery) -> Fee
                constructs Fee

            let baseFee (tier: Membership): Int =
                match tier with
                    | Premium -> 0
                    | Standard -> 500

            let expressFee (speed: Delivery): Int =
                match speed with
                    | Express -> 500
                    | Regular -> 0

            let shippingFee (member, delivery) =
                Fee(baseFee(member) + expressFee(delivery))

            example shippingFee
                | "a premium express parcel" : (Premium, Express) -> Fee(500)
            """;

    /**
     * An arm a combination of the body's own decisions takes is answered with the row that takes it.
     *
     * <p>Two searches used to be two worlds: the combinations composed rows before any finding was
     * consulted, and the finding about an arm was told nothing composes an input for one. Both were
     * true and they were about the same rows — a combination is a way through each of the forks it
     * reads, so a row composed for one takes an arm of each.
     */
    @Test
    void anArmACombinationTakesIsAnsweredWithTheRowThatTakesIt() {
        Compilation compilation = compiled(SHIPPING);
        List<Adequacy.GenerationDisposition> arms =
                filling(compilation, "example.shipping", "shippingFee").generation().stream()
                        .filter(d -> d.finding().kind() == Adequacy.Kind.ARM_UNREACHED).toList();

        assertFalse(arms.isEmpty(), "no row is written, so every arm is unreached");
        assertTrue(arms.stream().allMatch(
                        d -> d.outcome() instanceof GenerationOutcome.Generated),
                "each is answered with the row composed for a combination that takes it: " + arms);
    }

    @Test
    void anArmNoStrategyReachesIsNotSupportedRatherThanUnanswered() {
        Compilation compilation = compiled(POLICY);
        List<Adequacy.GenerationDisposition> arms =
                filling(compilation, "example.policy", "fee").generation().stream()
                        .filter(d -> d.finding().kind() == Adequacy.Kind.ARM_UNREACHED).toList();

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

    /**
     * The same, with a case an axis divides and no value gets past its rules.
     *
     * <p>The case is composed field by field like any other and every candidate is refused at
     * construction, so what comes back is a search that ran and a reason for what it found.
     */
    private static final String CARRIED = """
            module example.pay

            data Amount = Decimal
                invariant value >= 0.0m

            data Card = { holder: Amount }
                invariant notFree = holder.value /= 0.0m
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
        return filling(compilation, module, behavior).generation().stream()
                .filter(each -> each.finding().about()
                        instanceof souther.compiler.query.About.ACaseNoRowAppliesItTo(
                                var input, var case_)
                        && case_.name().equals(missing) && input.at() + 1 == at)
                .map(Adequacy.GenerationDisposition::outcome)
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
     * news of a different kind. Reading it as "no strategy for this" would say the generator will
     * never offer a row at a class it took and searched.
     *
     * <p>A card has values — any amount above none is one — and the search proposes the end of the
     * range, which is the one amount the rule refuses. So this is what the search could not reach and
     * not what has no value: a type with none is refused before any of this, and a fixture that had
     * none would be asking the generator about a model that does not compile. Should the search learn
     * to step off an end it was refused at, this becomes a row, which is the answer changing for the
     * reason it should.
     */
    @Test
    void aCaseNothingComposedAValueForIsAnsweredByTheAttempt() {
        GenerationOutcome answer = forCase(compiled(CARRIED), "example.pay", "feeFor", "Card", 1);

        assertInstanceOf(GenerationOutcome.CannotGenerate.class, answer);
    }

    /**
     * Every case of a sum parameter is offered a row, however many positions the behavior takes.
     *
     * <p>What used to be here asserted the other half of this: a limit on how many positions one
     * behavior is measured at left the thirteenth without an axis, and its cases were answered
     * {@code NO_AXIS_AT_THIS_POSITION}. That limit is gone (#969) and with it the only reading that
     * produced a case at a position nothing divided, so what is left to hold is that the thirteenth
     * is offered a row like the first.
     */
    @Test
    void everyCaseOfASumParameterIsOfferedARow() {
        Compilation compilation = compiled(WIDE);

        assertInstanceOf(GenerationOutcome.Generated.class,
                forCase(compilation, "example.wide", "pick", "Overseas", 1),
                "the first position is divided and offered");
        assertInstanceOf(GenerationOutcome.Generated.class,
                forCase(compilation, "example.wide", "pick", "Overseas", 13),
                "and so is the thirteenth");
    }

    /**
     * And what each of them says is what is missing here.
     *
     * <p>The words, because the words are the contract at this point. This type's own javadoc says
     * these are strategies that could exist and do not, and that none of them says the gap cannot
     * be met — while the sentence for an arm said nothing composes an input for it, of a row an
     * author writes in two lines (issue #643). A reader who writes that row must not be
     * contradicting the report.
     *
     * <p>Held one by one rather than by a rule over the strings, because there is no property of a
     * sentence that says it is about a compiler. What there is, is a person reading each of them
     * next to what it is written for.
     */
    @Test
    void eachReasonSaysWhatIsMissingHereRatherThanWhatCannotExist() {
        assertEquals("rows here are composed for the classes a position divides into, for the"
                        + " combinations this body settles together and for boundaries, and no"
                        + " combination of them takes this arm",
                GenerationOutcome.NotSupported.Reason.NO_COMBINATION_REACHES_THIS_ARM.said());
        assertEquals("rows here are composed from what the input positions divide into, and nothing"
                        + " searches for one by the case it would answer with",
                GenerationOutcome.NotSupported.Reason.NO_STRATEGY_FOR_AN_OUTPUT_CASE.said());
        // A case whose parameter no axis was derived at has its cases in the declaration and in no
        // partition, so what is missing is a derivation and not the classes. Said as there being
        // none, the sentence is about the model again — the thing the other two stopped doing.
        assertEquals("no axis was derived at the position this case belongs to, so no classes were"
                        + " derived there to compose a row from",
                GenerationOutcome.NotSupported.Reason.NO_AXIS_AT_THIS_POSITION.said());
    }

    @Test
    void aCaseOfTheOutputIsNotSupported() {
        List<GenerationOutcome> outputs = filling(compiled(KIND), "example.kind", "pick").generation()
                .stream()
                .filter(each -> each.finding().kind() == Adequacy.Kind.OUTPUT_CASE_UNSPECIFIED)
                .map(Adequacy.GenerationDisposition::outcome).toList();

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
                Map.of(), true, SourceNameResolver.identity()).text();
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
        String block = GeneratedRows.of("example.policy", generated, Map.of(), true, SourceNameResolver.identity()).text();

        assertTrue(block.contains("`then`"),
                "the arm nothing offers a row for is named: " + block);
    }
}
