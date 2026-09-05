package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;
import souther.compiler.source.SourceId;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The readers that find a rule with no line put their findings in one place, which keeps every
 * handle and holds the two halves apart.
 *
 * <p>One fold for six readers. A rule found by two of them is one thing with both of their handles
 * beside it, and what makes two findings one is the rule, the place and the limit — so a fold each
 * reader wrote for itself would keep whichever handle it met first, and a fold further down could
 * only accumulate what those let through.
 *
 * <p>And two lists there, folded apart. What a report says about a rule that came to no line and
 * what holds a measure open until somebody reads further are different things about one rule, so
 * neither is an account of the other and each is folded on its own.
 *
 * <p>Asked of the fold and not of a report, so that it says something about a rule found twice
 * whether or not this compiler's readers do that today.
 */
class OneIdentityIsFoldedOnceAndKeepsEveryHandleTest {

    private static final RuleCitation NAMED = new RuleCitation.Named("n");
    private static final RuleCitation PLACED =
            new RuleCitation.WrittenAt(Citation.of(new SourcePos(3, 3)));

    @Test
    void oneRuleFoundTwiceIsOneFindingCitedBothWays() {
        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        gathered.add(found(NAMED, "x"));
        gathered.add(found(PLACED, "x"));

        assertEquals(1, gathered.found().reported().size(),
                () -> "one rule at one position for one reason is one finding: "
                        + gathered.found().reported());
        assertEquals(Set.of(NAMED, PLACED), gathered.found().reported().get(0).cited(),
                "and a reader can be sent to it either way either reader offered");
    }

    /** Which of the two was found first decides nothing about what comes out. */
    @Test
    void whichReaderFoundItFirstDecidesNothing() {
        RulesWithNoLine.Gathered one = new RulesWithNoLine.Gathered();
        one.add(found(NAMED, "x"));
        one.add(found(PLACED, "x"));
        RulesWithNoLine.Gathered theOtherWayRound = new RulesWithNoLine.Gathered();
        theOtherWayRound.add(found(PLACED, "x"));
        theOtherWayRound.add(found(NAMED, "x"));

        assertEquals(one.found(), theOtherWayRound.found(),
                "and what each hands on is one value, which compares by what is in it");
    }

    /** And two rules are two findings, so the fold is on the rule and not on everything at once. */
    @Test
    void twoRulesAreTwoFindings() {
        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        gathered.add(found(NAMED, "x"));
        gathered.add(found(NAMED, "y"));

        assertEquals(2, gathered.found().reported().size(), () -> gathered.found().reported().toString());
    }

    /** And nothing puts together two findings that are not one rule. */
    @Test
    void twoFindingsThatAreNotOneRuleAreNotPutTogether() {
        RuleWithoutALine here = found(NAMED, "x");
        RuleWithoutALine elsewhere = found(NAMED, "y");

        assertThrows(IllegalArgumentException.class, () -> here.mergedWith(elsewhere));
    }

    /**
     * A question about a rule nothing classified is folded the way a finding is, and beside them.
     *
     * <p>Two lists and one fold each. What a report says about a rule and what holds a measure open
     * are different things about it, so one is no account of the other — and a rule met twice is
     * one entry in whichever of them it is in, with both handles.
     */
    @Test
    void aQuestionAboutAnUnclassifiedRuleIsFoldedBesideTheFindings() {
        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        gathered.unclassified(comparison(), NAMED, at("x"), new BlockReason.UnreadComparisonForm());
        gathered.unclassified(comparison(), PLACED, at("x"),
                new BlockReason.UnreadComparisonForm());
        gathered.add(comparison(), NAMED, at("x"), new BlockReason.ComparisonBetweenPositions());

        assertEquals(1, gathered.found().unclassified().size(),
                () -> "one rule, one place, one limit: " + gathered.found().unclassified());
        assertEquals(Set.of(NAMED, PLACED), gathered.found().unclassified().get(0).cited(),
                "and both handles are kept, as they are for a finding");
        assertEquals(1, gathered.found().reported().size(),
                () -> "the rule read to the end is beside it and not folded into it: "
                        + gathered.found().reported());
    }

    /** A question two readers cited two ways is one question with both handles, and what the author
     *  wrote it short of is untouched. */
    @Test
    void oneQuestionCitedTwoWaysKeepsBothHandlesAndTheAuthorsOrder() {
        StandingQuestion both = asked(NAMED, standingOn()).mergedWith(asked(PLACED, standingOn()));

        assertEquals(Set.of(NAMED, PLACED), both.cited());
        assertEquals(standingOn(), both.stopped());
    }

    /** And two accounts of one question that disagree about that order are not put together. */
    @Test
    void twoAccountsOfOneQuestionCannotDisagreeAboutWhatTheAuthorWrote() {
        BlockReason.RuleReadingStopped form = new BlockReason.UnreadComparisonForm();
        BlockReason.RuleReadingStopped domain = new BlockReason.UnreadComparisonDomain();
        StandingQuestion one = asked(NAMED, standingOn(form, domain));
        StandingQuestion theOtherWayRound = asked(PLACED, standingOn(domain, form));

        assertThrows(TwoAccountsOfOneQuestion.class, () -> one.mergedWith(theOtherWayRound));
    }

    /**
     * And an account that met the answer's limit is not disagreeing with one that did not.
     *
     * <p>What the position's answer was short of is a fact about what the rules of that position
     * come to between them, and the two accounts are of one rule. A reading whose neighbours left
     * the answer buildable met no such limit and one reached where they did, and neither of them is
     * wrong — so the question stands on what either met, and a model somebody could write does not
     * refuse to compile because two readings of one rule found different things about a position
     * neither is answerable for.
     */
    @Test
    void anAccountThatMetTheAnswersLimitIsNotDisagreeingWithOneThatDidNot() {
        StandingQuestion both = asked(NAMED, standingOn())
                .mergedWith(asked(PLACED, itsRuleAlone()));

        assertEquals(Set.of(NAMED, PLACED), both.cited());
        assertEquals(Optional.of(new BlockReason.ExactValuesTooCostly()),
                both.stopped().itsPositionWasShortOf(),
                "the question stands on it, and it was met once");
    }

    /** And two that met different limits are disagreeing about the position. */
    @Test
    void andTwoThatMetDifferentLimitsAreRefused() {
        StandingQuestion one = asked(NAMED, standingOn());
        StandingQuestion other = asked(PLACED, new WhatAQuestionStandsOn(
                RuleReasons.one(new BlockReason.UnreadComparisonForm()),
                Optional.of(new BlockReason.RulesNotHandedOnAsSets())));

        assertThrows(TwoAccountsOfOneQuestion.class, () -> one.mergedWith(other));
    }

    /** The same question, met where its position's answer was worked out. */
    private static WhatAQuestionStandsOn itsRuleAlone() {
        return new WhatAQuestionStandsOn(
                RuleReasons.one(new BlockReason.UnreadComparisonForm()), Optional.empty());
    }

    /** And a question that asks something is not an account of one that asks nothing. */
    @Test
    void theTwoKindsOfStandingQuestionAreNotTwoAccountsOfOneThing() {
        StandingQuestion asks = asked(NAMED, standingOn());
        StandingQuestion unclassified = StandingQuestion.NothingClassifiesIt.of(
                comparison(), NAMED, at("x"), new BlockReason.UnreadComparisonForm());

        assertThrows(IllegalArgumentException.class, () -> asks.mergedWith(unclassified));
        assertThrows(IllegalArgumentException.class, () -> unclassified.mergedWith(asks));
    }

    /**
     * And what stopped a reading here is asked of both lists, because either can be the only one
     * saying so.
     *
     * <p>A rule whose questions an accounting raised leaves a finding and no question of this kind;
     * a rule nothing classified leaves a question and no finding. A caller reading one list for
     * this is told nothing at a place holding the other, and hands the values there on as what the
     * rules leave.
     */
    @Test
    void whatStoppedAReadingIsAskedOfTheFindingsAndOfTheQuestions() {
        BlockReason.RuleReadingStopped form = new BlockReason.UnreadComparisonForm();
        RulesWithNoLine.Gathered asFinding = new RulesWithNoLine.Gathered();
        asFinding.add(comparison(), NAMED, at("x"), form);
        RulesWithNoLine.Gathered asQuestion = new RulesWithNoLine.Gathered();
        asQuestion.unclassified(comparison(), NAMED, at("x"), form);

        assertEquals(null, RulesWithNoLine.NONE.aReadingThatStopped(),
                "nothing found, so nothing stopped");
        assertEquals(form, asFinding.found().aReadingThatStopped(),
                "a rule the accounting asked about leaves the finding and no question of that kind");
        assertEquals(form, asQuestion.found().aReadingThatStopped(),
                "and a rule nothing classified leaves the question and no finding");
    }

    /** And a rule read from end to end stopped nothing, which is the sentence it is not. */
    @Test
    void aRuleReadFromEndToEndStoppedNothing() {
        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        gathered.add(found(NAMED, "x"));

        assertEquals(null, gathered.found().aReadingThatStopped(),
                () -> "the reading got through it: " + gathered.found().reported());
    }

    private static RuleWithoutALine found(RuleCitation cited, String at) {
        return RuleWithoutALine.of(comparison(), cited, at(at),
                new BlockReason.ComparisonBetweenPositions());
    }

    private static FilingCoordinate at(String path) {
        return new FilingCoordinate.AtPosition(TermPath.of(path));
    }

    private static StandingQuestion asked(RuleCitation cited, WhatAQuestionStandsOn stopped) {
        return StandingQuestion.Exact.of(comparison(), cited,
                new InputQuestion.AboutAPosition(TermPath.of("x")), stopped);
    }

    /** One question short in both ways, which is what a fold has to keep whole. */
    private static WhatAQuestionStandsOn standingOn() {
        return new WhatAQuestionStandsOn(
                RuleReasons.one(new BlockReason.UnreadComparisonForm()),
                Optional.of(new BlockReason.ExactValuesTooCostly()));
    }

    /** One question short in as many ways as somebody wrote, in the order they wrote them. */
    private static WhatAQuestionStandsOn standingOn(BlockReason.RuleReadingStopped... these) {
        List<RuleReasons.Placed> written = new ArrayList<>();
        for (int i = 0; i < these.length; i++) {
            written.add(new RuleReasons.Placed(
                    new SourcePos(1, i + 1, new SourceId("one")), these[i]));
        }
        return new WhatAQuestionStandsOn(RuleReasons.from(written), Optional.empty());
    }

    private static RuleRef comparison() {
        return new RuleRef.Comparison("b", new SourceConstructOrigin("m", 1, 1, SourceConstruct.IF));
    }
}
