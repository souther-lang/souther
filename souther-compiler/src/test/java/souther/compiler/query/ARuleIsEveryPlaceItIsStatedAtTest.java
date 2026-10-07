package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.Generator;
import souther.compiler.partition.MeasuredInput;
import souther.compiler.partition.WhereNothingIsAnswered;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

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
            return new DecisionReading.Ruled(rule, way.shownBy(), way.states(), way.demands(),
                    way.whole());
        }

        /** The body's reading with {@code more} beside its own ways. */
        DecisionReading with(DecisionReading.Ruled... more) {
            List<DecisionReading.Ruled> found = new ArrayList<>(read.found());
            found.addAll(Arrays.asList(more));
            return new DecisionReading(read.behavior(), found, read.enumeration());
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
        RuleSettlement excluded = RuleSettlement.provedNothingTakesIt(
                RuleSearch.CameToNothing.of(List.of(new Generator.UnresolvedCombination(
                        List.of("a rule of the decision"),
                        Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE))));
        RuleSettlement elsewhere = RuleSettlement.of(
                new RuleRequirement.Unsettled.AComposedRowWentElsewhere(),
                CompositionAccount.NOTHING);

        assertInstanceOf(RuleRequirement.Unsettled.AComposedRowWentElsewhere.class,
                Adequacy.DecisionSearch.acrossThePlaces(List.of(excluded, elsewhere))
                        .requirement(), "one place a row may take settles nothing away");
        assertInstanceOf(RuleRequirement.Unsettled.AComposedRowWentElsewhere.class,
                Adequacy.DecisionSearch.acrossThePlaces(List.of(elsewhere, excluded))
                        .requirement(), "whichever place was met first");
        assertTrue(Adequacy.DecisionSearch.acrossThePlaces(List.of(excluded, excluded))
                .requirement() instanceof RuleRequirement.Excluded);
        assertNull(Adequacy.DecisionSearch.acrossThePlaces(Arrays.asList(excluded, null)),
                "a place not searched for is not one the model leaves no row");
    }
}
