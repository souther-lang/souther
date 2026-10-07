package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.WhereNothingIsAnswered;
import souther.compiler.query.Adequacy;
import souther.compiler.query.ArmDisposition;
import souther.compiler.query.ArmObligation;
import souther.compiler.query.ArmSummary;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ObligationDisposition;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.AdequacyUncertainty;
import souther.compiler.report.ArmVocabulary;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An arm, a rule, a combination of decisions and a point of a line every row of which reaches an
 * {@code unreachable} are counted and undecided, as a class is.
 *
 * <p>What an obligation asks for is a set of rows, and the question is the same whatever kind of
 * obligation it is: whether every one of them is in a part of the body that answers nothing, those
 * parts taken together. Where it is, a row meeting the obligation is refused (E1911), so the
 * obligation is no gap; and nothing proves the inputs there do not arise, so it is not taken out of
 * the count either. It is open on the premises the body states.
 *
 * <p>Every row and every occurrence. A row an obligation asks for may arrive by any way the body has
 * to it, through any call of a helper and under any reading of a line, so one of those ways that
 * answers is a row that can be written — and the obligation is a gap like any other. Each case
 * below has the control beside it that leaves one such row.
 */
class AnObligationOfAnyKindEveryRowOfWhichReachesAnUnreachableIsUndecidedTest {

    /**
     * Two parts that each answer nothing for one value of {@code c}, so
     * every row through {@code case Q} aborts at one or the other, and neither part holds them all.
     */
    private static final String SPLIT = """
            module example.half

            data X
            data Y
            data A = X | Y
            data P
            data Q
            data B = P | Q
            data On
            data Off
            data C = On | Off

            behavior f : (a: A, b: B, c: C) -> Int

            let f (a, b, c) =
                match a with
                    | X -> 1
                    | Y -> match b with
                             | P -> 2
                             | Q -> {
                                 let first = match c with
                                     | On  -> unreachable "never On here"
                                     | Off -> 3
                                 match c with
                                     | On  -> first
                                     | Off -> unreachable "never Off here"
                             }

            example f
                | "X P On"  : (X, P, On) -> 1
                | "X Q Off" : (X, Q, Off) -> 1
                | "Y P Off" : (Y, P, Off) -> 2
            """;

    /** The same with one part answering nothing: a row through {@code case Q} with {@code Off}
     *  answers {@code 3}. */
    private static final String HALF = SPLIT.replace("""
                             | Q -> {
                                 let first = match c with
                                     | On  -> unreachable "never On here"
                                     | Off -> 3
                                 match c with
                                     | On  -> first
                                     | Off -> unreachable "never Off here"
                             }
            """, """
                             | Q -> match c with
                                      | On  -> unreachable "never On here"
                                      | Off -> 3
            """);

    /** One helper called twice, and under the first call every row with {@code On} aborts. */
    private static final String HELPER = """
            module example.helper

            data X
            data Y
            data A = X | Y
            data On
            data Off
            data C = On | Off

            let pick (c: C): Int =
                match c with
                    | On  -> 1
                    | Off -> 2

            behavior f : (a: A, c: C) -> Int

            let f (a, c) =
                match a with
                    | X -> {
                        let p = pick(c)
                        match c with
                            | On  -> unreachable "never X On"
                            | Off -> p
                    }
                    | Y -> {
                        let q = pick(c)
                        match c with
                            | On  -> q
                            | Off -> q
                    }

            example f
                | "X Off" : (X, Off) -> 2
                | "Y Off" : (Y, Off) -> 2
            """;

    /** And under the second call as well. */
    private static final String HELPER_EVERYWHERE = HELPER.replace(
            "| On  -> q", "| On  -> unreachable \"never Y On\"");

    /**
     * A rule and a combination of decisions every row of which aborts at one of two parts off the
     * way to the answer: {@code Y} with {@code On} aborts with {@code P} at the first and with
     * {@code Q} at the second.
     */
    private static final String OFF_THE_WAY = """
            module example.off

            data X
            data Y
            data A = X | Y
            data P
            data Q
            data B = P | Q
            data On
            data Off
            data C = On | Off

            behavior f : (a: A, b: B, c: C) -> Int

            let f (a, b, c) = {
                let first = match a with
                    | X -> 0
                    | Y -> match c with
                             | On  -> match b with
                                        | P -> unreachable "never Y P On"
                                        | Q -> 0
                             | Off -> 0
                let second = match a with
                    | X -> 0
                    | Y -> match c with
                             | On  -> match b with
                                        | Q -> unreachable "never Y Q On"
                                        | P -> 0
                             | Off -> 0
                %s
            }

            example f
                | "X P On"  : (X, P, On) -> %s
                | "X P Off" : (X, P, Off) -> %s
                | "Y P Off" : (Y, P, Off) -> %s
            """;

    /** The rules of a decision the answer is settled by. */
    private static final String RULE = OFF_THE_WAY.formatted("""
            match a with
                    | X -> 1
                    | Y -> match c with
                             | On  -> 2
                             | Off -> 3""", "1", "1", "3");

    /** Two decisions meeting at one operator. */
    private static final String MEETING = OFF_THE_WAY.formatted("""
            let left = match a with
                    | X -> 1
                    | Y -> 2
                let right = match c with
                    | On  -> 10
                    | Off -> 20
                left + right""", "11", "21", "22");

    /** A line drawn on {@code n}, every row reaching which aborts at one of two parts. */
    private static final String LINE = """
            module example.line

            data X
            data Y
            data A = X | Y
            data On
            data Off
            data C = On | Off

            behavior f : (a: A, c: C, n: Int) -> Int

            let f (a, c, n) =
                match a with
                    | X -> {
                        let first = match c with
                            | On  -> unreachable "never On"
                            | Off -> 0
                        let second = match c with
                            | On  -> 0
                            | Off -> unreachable "never Off"
                        if n > 10 then first + second + 1 else first + second + 2
                    }
                    | Y -> 3

            example f
                | "Y" : (Y, On, 0) -> 3
            """;

    /** The same body forking on a comparison of two inputs, which no class of either divides. */
    private static final String UNPLACED = LINE
            .replace("behavior f : (a: A, c: C, n: Int)", "behavior f : (a: A, c: C, n: Int, m: Int)")
            .replace("let f (a, c, n)", "let f (a, c, n, m)")
            .replace("if n > 10", "if n > m")
            .replace("(Y, On, 0) -> 3", "(Y, On, 0, 0) -> 3");

    /** The second part answering, so a row with {@code Off} at the line answers. */
    private static final String LINE_ANSWERED = LINE.replace(
            "| Off -> unreachable \"never Off\"", "| Off -> 0");

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static ArmSummary armsOf(Compilation compilation) {
        Adequacy.BranchEvidence arms = compilation.db()
                .ask(new Adequacy.BranchCoverage(compilation.modules().get(0))).value().get("f");
        assertNotNull(arms, "the model under test has arms");
        return arms.arms();
    }

    /** The counted arm written as {@code label}, by the words a report names it with. */
    private static List<ArmObligation.Counted> armsCalled(ArmSummary arms, String label) {
        return arms.all().stream()
                .filter(ArmObligation.Counted.class::isInstance)
                .map(ArmObligation.Counted.class::cast)
                .filter(arm -> ArmVocabulary.label(arm.display()).equals(label))
                .toList();
    }

    /** What the premises an obligation rests on say, each part once, in the order met. */
    private static List<String> said(List<WhereNothingIsAnswered.Premise> premises) {
        return premises.stream().flatMap(each -> each.reasons().stream()).toList();
    }

    private static List<Adequacy.Finding> findingsOfKind(Compilation compilation,
                                                         Adequacy.Kind kind) {
        return AdequacyReport.of(compilation).findings().stream()
                .filter(each -> each.kind() == kind).toList();
    }

    private static String offeredFor(Compilation compilation) {
        return GeneratedRows.of(compilation, compilation.modules().get(0), "f",
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
    }

    /**
     * The three arms whose rows abort are undecided, each on the parts its rows reach.
     *
     * <p>{@code case Q} rests on both parts, which is the union: neither holds every row through
     * it. The two arms of the second {@code match} each rest on the part their rows abort at.
     */
    @Test
    void theArmsEveryRowThroughWhichAbortsAreUndecidedOnWhatTheyRestOn() {
        ArmSummary arms = armsOf(measured(SPLIT));

        assertEquals(List.of("never On here", "never Off here"),
                said(armsCalled(arms, "case Q").getFirst().premises()));
        for (String label : List.of("case Q", "case On", "case Off")) {
            for (ArmObligation.Counted arm : armsCalled(arms, label)) {
                assertEquals(ArmDisposition.UNDECIDED, arm.disposition(),
                        () -> label + " is open on " + arm.premises());
            }
        }
        assertEquals(List.of(), arms.unmet(), "no arm here is one a row can be written through");
    }

    /** The count is what it was: the arms are still owed, and no row goes through them. */
    @Test
    void theArmsAreStillCounted() {
        ArmSummary arms = armsOf(measured(SPLIT));

        assertEquals(6, arms.counted());
        assertEquals(3, arms.covered());
    }

    /**
     * And a build is told what the arms are open on, and is not refused over them.
     *
     * <p>The verdict is refused over the pairs no row is in, which are gaps; what is asked here is
     * that no arm is among them and that the premises are among what the analysis left open.
     */
    @Test
    void noArmIsRefusedOverAndWhatTheyAreOpenOnIsSaid() {
        Compilation compilation = measured(SPLIT);
        AdequacyReport report = AdequacyReport.of(compilation);

        assertTrue(report.adequacyGaps().stream()
                        .noneMatch(each -> each.kind() == Adequacy.Kind.ARM_UNREACHED),
                () -> report.adequacyGaps().toString());
        Set<String> open = report.assessment().uncertainties().stream()
                .filter(AdequacyUncertainty.EveryRowReachesAnUnreachable.class::isInstance)
                .map(each -> ((AdequacyUncertainty.EveryRowReachesAnUnreachable) each).premise())
                .flatMap(premise -> premise.reasons().stream())
                .collect(Collectors.toSet());
        assertEquals(Set.of("never On here", "never Off here"), open);
        String page = report.human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        assertTrue(page.contains("? undecided whether a row goes through `case Q` (null): a row"
                + " there reaches `unreachable` (never On here; never Off here)"), page);
    }

    /** Nothing is offered for an arm every row through which is refused. */
    @Test
    void nothingIsOfferedThroughThem() {
        String offered = offeredFor(measured(SPLIT));

        assertFalse(offered.contains("case Q"), offered);
        assertFalse(offered.contains("(Y, Q"), offered);
    }

    /** The control: with a row through {@code case Q} that answers, the arm is a gap. */
    @Test
    void anArmARowCanBeWrittenThroughIsAGap() {
        ArmObligation.Counted q = armsCalled(armsOf(measured(HALF)), "case Q").getFirst();

        assertEquals(ArmDisposition.UNMET, q.disposition(), () -> "open on " + q.premises());
    }

    /**
     * An arm of a helper is every call of it. A row through the arm under the second call answers,
     * so the arm is a gap however every row under the first call fares.
     */
    @Test
    void aHelpersArmOneCallOfWhichAnswersIsAGap() {
        ArmSummary arms = armsOf(measured(HELPER));
        List<ArmObligation.Counted> picked = armsCalled(arms, "case On").stream()
                .filter(arm -> arm.occurrences().size() == 2).toList();

        assertEquals(1, picked.size(), () -> "the helper's arm, at both calls: " + arms.all());
        assertEquals(ArmDisposition.UNMET, picked.getFirst().disposition(),
                () -> "open on " + picked.getFirst().premises());
    }

    /** And where every row under each call aborts, the arm is undecided on both parts. */
    @Test
    void aHelpersArmEveryCallOfWhichAbortsIsUndecided() {
        ArmSummary arms = armsOf(measured(HELPER_EVERYWHERE));
        List<ArmObligation.Counted> picked = armsCalled(arms, "case On").stream()
                .filter(arm -> arm.occurrences().size() == 2).toList();

        assertEquals(ArmDisposition.UNDECIDED,
                picked.getFirst().disposition());
        assertEquals(List.of("never X On", "never Y On"), said(picked.getFirst().premises()));
    }

    /**
     * A condition on the way that no class places keeps the rows it would have left out, and does
     * not take the way with it.
     *
     * <p>The rows through {@code then} are every row with {@code X} and {@code n} above {@code m},
     * and no class says which those are; read as every row with {@code X}, they are still inside
     * the two parts. Read as no row instead — the way left out for what it could not place — the arm
     * would rest on nothing and be a gap no row can close.
     */
    @Test
    void aConditionNoClassPlacesWidensTheWayAndDoesNotDropIt() {
        ArmSummary arms = armsOf(measured(UNPLACED));

        for (String label : List.of("then", "else")) {
            ArmObligation.Counted arm = armsCalled(arms, label).getFirst();
            assertEquals(ArmDisposition.UNDECIDED, arm.disposition(), label);
            assertEquals(List.of("never On", "never Off"), said(arm.premises()), label);
        }
    }

    /**
     * A rule two parts hold between them is undecided, and a row is not composed for it: the row
     * would be refused, and what a search of it came to would be said in place of the premise.
     */
    @Test
    void aRuleTwoPartsHoldBetweenThemIsUndecided() {
        Compilation compilation = measured(RULE);
        List<Adequacy.Finding> rules =
                findingsOfKind(compilation, Adequacy.Kind.DECISION_RULE_UNCOVERED);

        assertEquals(1, rules.size(), rules::toString);
        assertEquals(Adequacy.Finding.Disposition.UNDECIDED, rules.getFirst().disposition());
        assertEquals(List.of("never Y P On", "never Y Q On"), said(rules.getFirst().premises()));
        assertTrue(rules.getFirst().weakenedBy().isEmpty(),
                "the rules were read in full; what is open is the rule");
        assertEquals(1, unansweredRulesOf(compilation).size());
    }

    /**
     * The control: with one part answering, no rule rests on a premise, and the rule is left to
     * what its search comes to.
     */
    @Test
    void aRuleOneRowOfWhichAnswersRestsOnNothing() {
        Compilation compilation = measured(RULE.replace(
                "| Q -> unreachable \"never Y Q On\"", "| Q -> 0"));

        assertEquals(Map.of(), unansweredRulesOf(compilation));
        assertTrue(findingsOfKind(compilation, Adequacy.Kind.DECISION_RULE_UNCOVERED).stream()
                .allMatch(each -> each.premises().isEmpty()));
    }

    private static Map<?, ?> unansweredRulesOf(Compilation compilation) {
        return compilation.db().ask(new Adequacy.Decides(compilation.modules().get(0))).value()
                .get("f").unanswered();
    }

    /** A combination of decisions two parts hold between them is undecided. */
    @Test
    void aCombinationTwoPartsHoldBetweenThemIsUndecided() {
        Compilation compilation = measured(MEETING);
        List<Adequacy.Finding> meetings =
                findingsOfKind(compilation, Adequacy.Kind.INTERACTION_UNCOVERED);

        assertEquals(1, meetings.size(), meetings::toString);
        assertEquals(Adequacy.Finding.Disposition.UNDECIDED, meetings.getFirst().disposition());
        assertEquals(List.of("never Y P On", "never Y Q On"),
                said(meetings.getFirst().premises()));
        assertFalse(offeredFor(compilation).contains("(Y, Q, On)"));
    }

    /** The control: with one part answering, the combination is a gap. */
    @Test
    void aCombinationOneRowOfWhichAnswersIsAGap() {
        List<Adequacy.Finding> meetings = findingsOfKind(measured(MEETING.replace(
                "| Q -> unreachable \"never Y Q On\"", "| Q -> 0")),
                Adequacy.Kind.INTERACTION_UNCOVERED);

        assertEquals(1, meetings.size(), meetings::toString);
        assertEquals(Adequacy.Finding.Disposition.REFUSED, meetings.getFirst().disposition());
    }

    /** Every point of a line every row reaching which aborts is undecided on both parts. */
    @Test
    void aPointEveryRowAtWhichAbortsIsUndecided() {
        Compilation compilation = measured(LINE);
        List<BorderObligationPointAssessment> points = pointsOf(compilation);
        String offered = offeredFor(compilation);
        assertFalse(offered.contains("n = 11"), offered);

        assertEquals(4, points.size(), points::toString);
        for (BorderObligationPointAssessment point : points) {
            ObligationDisposition.Undecided open = assertInstanceOf(
                    ObligationDisposition.Undecided.class, point.owed().disposition());
            assertTrue(open.because().written().stream().anyMatch(each -> each
                            instanceof ObligationDisposition.Uncertainty.WhetherARowCanBeWritten
                                    .EveryRowReachesAnUnreachable(var premises)
                            && said(premises).equals(List.of("never On", "never Off"))),
                    () -> point.role() + " is open on " + open);
            assertFalse(point.owed().worthSearching(), "a row there is refused");
        }
    }

    /** The control: with a row at the line that answers, no point is open on a premise. */
    @Test
    void aPointARowCanBeWrittenAtIsNotOpenOnAPremise() {
        for (BorderObligationPointAssessment point : pointsOf(measured(LINE_ANSWERED))) {
            assertTrue(!(point.owed().disposition() instanceof ObligationDisposition.Undecided open)
                            || open.because().written().stream().noneMatch(each -> each
                                    instanceof ObligationDisposition.Uncertainty
                                            .WhetherARowCanBeWritten.EveryRowReachesAnUnreachable),
                    () -> point.role() + " is " + point.owed().disposition());
        }
    }

    private static List<BorderObligationPointAssessment> pointsOf(Compilation compilation) {
        AdequacyReport report = AdequacyReport.of(compilation);
        Map<String, List<BorderObligationPointAssessment>> byBehavior = report.modules().stream()
                .flatMap(module -> module.behaviors().stream())
                .collect(Collectors.toMap(AdequacyReport.BehaviorReport::name,
                        AdequacyReport.BehaviorReport::account));
        return byBehavior.get("f");
    }
}
