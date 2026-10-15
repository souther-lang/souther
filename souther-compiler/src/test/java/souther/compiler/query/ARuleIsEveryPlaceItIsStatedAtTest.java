package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.partition.AnswersDemanded;
import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.ConditionGap;
import souther.compiler.partition.ConditionOccurrence;
import souther.compiler.partition.ConditionReportAnchor;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.Generator;
import souther.compiler.partition.MeasuredInput;
import souther.compiler.partition.SaidOnTheWay;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.ReachabilityGap;
import souther.compiler.partition.RowToRun;
import souther.compiler.partition.RuleStep;
import souther.compiler.partition.WhereNothingIsAnswered;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A rule of a decision is every place the body states it, and what is asked of the rule is asked of
 * all of them together.
 *
 * <p>A rule is told apart by the distinctions it consults and not by where they are written, so one
 * rule can stand at two places, and a row taking it at either takes it. The rows it asks for are the
 * rows of both places; it is excluded only where the model leaves both no row; it is one rule to
 * count and to publish. Read one place at a time, each of those is answered by whichever place a
 * walk met first or last.
 *
 * <p>Put to readings assembled from a compiled one. Nothing this compiler reads yet states one rule
 * at two places — a condition it has no words for is still told apart by where it stands — so the
 * second place is a real way of the same body standing under the first one's rule, which is the
 * shape the type admits and every reader of a rule has to answer for.
 */
class ARuleIsEveryPlaceItIsStatedAtTest {

    /**
     * Each rule of the last decision rests on one part that answers nothing or on none: {@code Y}
     * with {@code On} and {@code P} aborts at the first part, with {@code Q} at the second, and
     * {@code Y} with {@code Off} answers.
     */
    private static final String MODEL = """
            module example.ruled

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
                match a with
                    | X -> 1
                    | Y -> match c with
                             | On  -> match b with
                                        | P -> 2
                                        | Q -> 3
                             | Off -> 4
            }

            example f
                | "X P On"  : (X, P, On) -> 1
                | "Y P Off" : (Y, P, Off) -> 4
            """;

    /** The compiled pieces the readings below are assembled from. */
    private record Compiled(DecisionReading read, WhereNothingIsAnswered unanswered,
                            MeasuredInput.MeasuredAxes axes) {

        /** The way of the rule every row of which rests on the part saying {@code reason}. */
        DecisionReading.Ruled restingOn(String reason) {
            Map<DecisionRule, List<WhereNothingIsAnswered.Premise>> open =
                    DecisionEvidence.unansweredIn(read, unanswered, axes);
            for (DecisionReading.Ruled each : read.found()) {
                List<WhereNothingIsAnswered.Premise> premises = open.get(each.rule());
                if (premises != null && premises.size() == 1
                        && premises.getFirst().reasons().equals(List.of(reason))) {
                    return each;
                }
            }
            throw new AssertionError("no rule rests on `" + reason + "` alone: " + open);
        }

        /** A way of a rule every row of which some row can answer. */
        DecisionReading.Ruled answering() {
            Map<DecisionRule, List<WhereNothingIsAnswered.Premise>> open =
                    DecisionEvidence.unansweredIn(read, unanswered, axes);
            return read.found().stream().filter(each -> !open.containsKey(each.rule()))
                    .findFirst().orElseThrow();
        }

        /** {@code way} standing as a second place of {@code rule}. */
        static DecisionReading.Ruled under(DecisionRule rule, DecisionReading.Ruled way) {
            return new DecisionReading.Ruled(rule, way.steps(), way.whole());
        }

        /** The body's reading with {@code more} beside its own ways. */
        DecisionReading with(DecisionReading.Ruled... more) {
            List<DecisionReading.Ruled> found = new ArrayList<>(read.found());
            found.addAll(Arrays.asList(more));
            return new DecisionReading(read.behavior(), found, read.enumeration(), read.metAt());
        }
    }

    private static Compiled compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        DecisionEvidence decided =
                compilation.db().ask(new Adequacy.Decides(module)).value().get("f");
        assertNotNull(decided, "the body states a decision");
        return new Compiled(decided.read(),
                compilation.db().ask(new Adequacy.Unanswered(module, "f")).value(),
                Adequacy.subjectOf(compilation.db(), module, "f").axes());
    }

    /**
     * One place of a rule whose rows answer leaves the rule a gap, however every row at the other
     * place fares: a row taking it there is a row that can be written.
     */
    @Test
    void aRuleOnePlaceOfWhichAnswersRestsOnNothing() {
        Compiled body = compiled();
        DecisionReading.Ruled aborting = body.restingOn("never Y P On");
        DecisionReading twice =
                body.with(Compiled.under(aborting.rule(), body.answering()));

        assertFalse(DecisionEvidence.unansweredIn(twice, body.unanswered(), body.axes())
                        .containsKey(aborting.rule()),
                "the second place answers, so the rule is no premise's");
    }

    /** And where every row at both places aborts, the rule rests on what each place reaches. */
    @Test
    void aRuleEveryPlaceOfWhichAbortsRestsOnBoth() {
        Compiled body = compiled();
        DecisionReading.Ruled first = body.restingOn("never Y P On");
        DecisionReading twice =
                body.with(Compiled.under(first.rule(), body.restingOn("never Y Q On")));

        List<WhereNothingIsAnswered.Premise> premises = DecisionEvidence.unansweredIn(
                twice, body.unanswered(), body.axes()).get(first.rule());
        assertNotNull(premises, "every row of the rule aborts at one place or the other");
        assertEquals(List.of(List.of("never Y P On"), List.of("never Y Q On")),
                premises.stream().map(WhereNothingIsAnswered.Premise::reasons).toList());
    }

    /** One rule, once: counted and listed by the rule and not by the places. */
    @Test
    void aRuleStatedTwiceIsOneRule() {
        Compiled body = compiled();
        DecisionReading.Ruled first = body.restingOn("never Y P On");
        DecisionReading twice =
                body.with(Compiled.under(first.rule(), body.answering()));

        assertEquals(body.read().rules().size(), twice.rules().size());
        DecisionReading.Stated stated = twice.stated().stream()
                .filter(each -> each.rule().equals(first.rule())).findFirst().orElseThrow();
        assertEquals(2, stated.occurrences().size());
        assertEquals(first, stated.display(), "a reader is shown the place met first");
    }

    /**
     * Excluded only where the model leaves every place no row; a place it leaves open is the rule's
     * answer, and a place not searched for because every row aborts keeps the rule unsettled.
     */
    @Test
    void aRuleIsExcludedOnlyWhereEveryPlaceIs() {
        DecisionReading.Ruled at = compiled().answering();
        SettledAt excluded = new SettledAt(at, RuleSettlement.provedNothingTakesIt(
                RuleSearch.CameToNothing.of(List.of(CameToNothing.metNothing(
                        new Generator.UnresolvedCombination(List.of("a rule of the decision"),
                                Generator.UnresolvedCombination.Reason
                                        .NO_VALUE_CAN_STAND_THERE))))), Set.of());
        SettledAt elsewhere = new SettledAt(at, RuleSettlement.of(
                new RuleRequirement.Unsettled.AComposedRowWentElsewhere(),
                CompositionAccount.NOTHING), Set.of());

        assertEquals(new SettledAcross(List.of(elsewhere)),
                Adequacy.DecisionSearch.acrossThePlaces(List.of(excluded, elsewhere)),
                "one place a row may take settles nothing away, and is the place that answers");
        assertEquals(new SettledAcross(List.of(elsewhere)),
                Adequacy.DecisionSearch.acrossThePlaces(List.of(elsewhere, excluded)),
                "whichever place was met first");
        assertEquals(new SettledAcross(List.of(excluded, excluded)),
                Adequacy.DecisionSearch.acrossThePlaces(List.of(excluded, excluded)),
                "every place the model leaves no row says what left it none");
        assertNull(Adequacy.DecisionSearch.acrossThePlaces(Arrays.asList(excluded, null)),
                "a place not searched for is not one the model leaves no row");
    }

    /** A place something stood in answers the rule on its own, wherever it was met. */
    @Test
    void aPlaceSomethingStoodInIsTheRulesAnswerAlone() {
        DecisionReading.Ruled at = compiled().answering();
        SettledAt stood = new SettledAt(at, RuleSettlement.of(
                new RuleRequirement.Required(new RowToRun(List.of(), List.of())),
                CompositionAccount.NOTHING), Set.of());
        SettledAt nothingTried = new SettledAt(at, RuleSettlement.nothingToTryWith(
                cameToNothing(), CompositionAccount.NOTHING), Set.of());

        assertEquals(new SettledAcross(List.of(stood)),
                Adequacy.DecisionSearch.acrossThePlaces(List.of(nothingTried, stood)),
                "the row there settles the rule");
    }

    /**
     * Every place the model leaves open answers the rule, each with the place it was searched at:
     * the one that established the most first, whichever order the places were met in.
     *
     * <p>The one that established more is what the requirement is read off. The other is kept
     * beside it, because what its search came to is not what the first one's did — held as the
     * best place alone, it reached nobody.
     */
    @Test
    void everyOpenPlaceAnswersTheRuleTheBestFirst() {
        Compiled body = compiled();
        DecisionReading.Ruled first = body.answering();
        DecisionReading.Ruled second = Compiled.under(first.rule(), body.read().found().stream()
                .filter(each -> !each.equals(first)).findFirst().orElseThrow());
        SettledAt nothingTried = new SettledAt(first, RuleSettlement.nothingToTryWith(
                cameToNothing(), CompositionAccount.NOTHING), Set.of());
        SettledAt composed = new SettledAt(second, RuleSettlement.of(
                new RuleRequirement.Unsettled.AComposedRowWentElsewhere(),
                CompositionAccount.NOTHING), Set.of());

        assertEquals(new SettledAcross(List.of(composed, nothingTried)),
                Adequacy.DecisionSearch.acrossThePlaces(List.of(nothingTried, composed)),
                "the place that established more first, and the other beside it");
        assertEquals(new SettledAcross(List.of(composed, nothingTried)),
                Adequacy.DecisionSearch.acrossThePlaces(List.of(composed, nothingTried)),
                "whichever place was met first");
    }

    /**
     * What the search at each place went without is that place's, and nothing of the place beside
     * it.
     *
     * <p>Two places of one rule whose ways each decline a condition of their own. Each answers
     * for the rule with the conditions its own way went without: explained by the other place's
     * way, a search would be said to have gone without a condition it never met.
     */
    @Test
    void whatEachSearchWentWithoutIsItsOwnPlaces() {
        Compiled body = compiled();
        DecisionReading.Ruled first = body.answering();
        OnTheWay.Declined declinedFirst = declined(0);
        OnTheWay.Declined declinedSecond = declined(1);
        DecisionReading.Ruled one = new DecisionReading.Ruled(first.rule(),
                List.of(new RuleStep(first.steps().getFirst().shown(), List.of(declinedFirst),
                        AnswersDemanded.NOTHING, SaidOnTheWay.NONE)), true);
        DecisionReading.Ruled other = new DecisionReading.Ruled(first.rule(),
                List.of(new RuleStep(first.steps().getFirst().shown(), List.of(declinedSecond),
                        AnswersDemanded.NOTHING, SaidOnTheWay.NONE)), true);
        SettledAt nothingTried = new SettledAt(one, RuleSettlement.nothingToTryWith(
                cameToNothing(), CompositionAccount.NOTHING), Set.of());
        SettledAt composed = new SettledAt(other, RuleSettlement.of(
                new RuleRequirement.Unsettled.AComposedRowWentElsewhere(),
                CompositionAccount.NOTHING), Set.of());

        for (List<SettledAt> met : List.of(List.of(nothingTried, composed),
                List.of(composed, nothingTried))) {
            SettledAcross rule = Adequacy.DecisionSearch.acrossThePlaces(met);
            assertEquals(List.of(new ConditionGap.OfTheInput(
                            new ReachabilityGap.Unstated(declinedSecond))),
                    rule.places().get(0).leftOut(),
                    "the conditions of the place that established more, and none of the other's");
            assertEquals(List.of(new ConditionGap.OfTheInput(
                            new ReachabilityGap.Unstated(declinedFirst))),
                    rule.places().get(1).leftOut(),
                    "and the other place's own");
        }
    }

    /** A search of the rule that had nothing to try and met nothing of this compiler's. */
    private static RuleSearch.CameToNothing cameToNothing() {
        return RuleSearch.CameToNothing.of(List.of(CameToNothing.metNothing(
                new Generator.UnresolvedCombination(List.of("a rule of the decision"),
                        Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE))));
    }

    /** A condition of the decision's reading declined for a reason, named {@code which}. */
    private static OnTheWay.Declined declined(int which) {
        ConditionOccurrence condition =
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DECIDING, which);
        return new OnTheWay.Declined(condition,
                new ConditionReportAnchor.WhereTheReadingMetIt("example.ruled", condition),
                new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER));
    }
}
