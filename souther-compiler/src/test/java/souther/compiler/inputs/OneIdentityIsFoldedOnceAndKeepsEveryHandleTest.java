package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.PartId;
import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.types.WrittenOwner;
import souther.compiler.check.RuleRef;
import souther.compiler.observe.Figure;
import souther.compiler.observe.WorkFigure;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

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
 * <p>Two handles of one rule are two ways in and never a name and a way in. Which of the two ways a
 * rule is found is the rule's own answer, so a rule the author named has one handle however many
 * readers offered it, and one written rather than named has a handle per way a reading came in
 * through — a helper's comparison read from two calls.
 *
 * <p>And two lists there, folded apart. What a report says about a rule that came to no line and
 * what holds a measure open until somebody reads further are different things about one rule, so
 * neither is an account of the other and each is folded on its own.
 *
 * <p>Asked of the fold and not of a report, so that it says something about a rule found twice
 * whether or not this compiler's readers do that today.
 */
class OneIdentityIsFoldedOnceAndKeepsEveryHandleTest {

    private static final RuleCitation ONE_CALL =
            new RuleCitation.Written(comparison(),
                    new RuleReportAnchor.ByTheReadingThatMetIt("Main", "pick", 0));
    private static final RuleCitation ANOTHER_CALL =
            new RuleCitation.Written(comparison(),
                    new RuleReportAnchor.ByTheReadingThatMetIt("Main", "pick", 1));

    @Test
    void oneRuleFoundTwiceIsOneFindingCitedBothWays() {
        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        gathered.add(found(ONE_CALL, "x"));
        gathered.add(found(ANOTHER_CALL, "x"));

        assertEquals(1, gathered.found().reported().size(),
                () -> "one rule at one position for one reason is one finding: "
                        + gathered.found().reported());
        assertEquals(Set.of(ONE_CALL, ANOTHER_CALL), gathered.found().reported().get(0).cited(),
                "and a reader can be sent to it either way either reader offered");
    }

    /** Which of the two was found first decides nothing about what comes out. */
    @Test
    void whichReaderFoundItFirstDecidesNothing() {
        RulesWithNoLine.Gathered one = new RulesWithNoLine.Gathered();
        one.add(found(ONE_CALL, "x"));
        one.add(found(ANOTHER_CALL, "x"));
        RulesWithNoLine.Gathered theOtherWayRound = new RulesWithNoLine.Gathered();
        theOtherWayRound.add(found(ANOTHER_CALL, "x"));
        theOtherWayRound.add(found(ONE_CALL, "x"));

        assertEquals(one.found(), theOtherWayRound.found(),
                "and what each hands on is one value, which compares by what is in it");
    }

    /** And two rules are two findings, so the fold is on the rule and not on everything at once. */
    @Test
    void twoRulesAreTwoFindings() {
        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        gathered.add(found(ONE_CALL, "x"));
        gathered.add(found(ONE_CALL, "y"));

        assertEquals(2, gathered.found().reported().size(), () -> gathered.found().reported().toString());
    }

    /** And nothing puts together two findings that are not one rule. */
    @Test
    void twoFindingsThatAreNotOneRuleAreNotPutTogether() {
        RuleWithoutALine here = found(ONE_CALL, "x");
        RuleWithoutALine elsewhere = found(ONE_CALL, "y");

        assertThrows(IllegalArgumentException.class, () -> here.mergedWith(elsewhere));
    }

    /**
     * A rule is reached the way rules of its kind are reached, and a finding says so.
     *
     * <p>What the fold keeps is the rule once and the places beside it, so a handle it hands back
     * is of that rule and can be of no other. A rule the author named has no place to keep, and one
     * written rather than named has nowhere for a reader to be sent without one.
     */
    @Test
    void aRuleIsReachedTheWayItsKindIsReached() {
        assertThrows(IllegalArgumentException.class,
                () -> new RuleWithoutALine(
                        new RuleWithoutALine.Fact(comparison(), at("x"),
                                RuleSite.theRuleItself(),
                                new BlockReason.ComparisonRelatingTwoValues()),
                        Set.of(), List.of()),
                "a comparison nothing places is one nobody can be sent to look at");
        assertThrows(IllegalArgumentException.class,
                () -> new RuleWithoutALine(
                        new RuleWithoutALine.Fact(invariant(), at("x"),
                                RuleSite.theRuleItself(),
                                new BlockReason.ComparisonRelatingTwoValues()),
                        Set.of(new RuleReportAnchor.ByTheModuleThatWroteIt()), List.of()),
                "and a question about where a rule the author named is written is a second way to"
                        + " say one thing");
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
        gathered.unclassified(ONE_CALL, List.of(), at("x"),
                new BlockReason.UnreadComparisonForm());
        gathered.unclassified(ANOTHER_CALL, List.of(), at("x"),
                new BlockReason.UnreadComparisonForm());
        gathered.add(ONE_CALL, at("x"), new BlockReason.ComparisonRelatingTwoValues());

        assertEquals(1, gathered.found().unclassified().size(),
                () -> "one rule, one place, one limit: " + gathered.found().unclassified());
        assertEquals(Set.of(ONE_CALL, ANOTHER_CALL),
                gathered.found().unclassified().get(0).cited(),
                "and both handles are kept, as they are for a finding");
        assertEquals(1, gathered.found().reported().size(),
                () -> "the rule read to the end is beside it and not folded into it: "
                        + gathered.found().reported());
    }

    /** A question two readers cited two ways is one question with both handles, and what the author
     *  wrote it short of is untouched. */
    @Test
    void oneQuestionCitedTwoWaysKeepsBothHandlesAndTheAuthorsOrder() {
        StandingQuestion both = asked(ONE_CALL, standingOn())
                .mergedWith(asked(ANOTHER_CALL, standingOn()));

        assertEquals(Set.of(ONE_CALL, ANOTHER_CALL), both.cited());
        assertEquals(standingOn(), both.stopped());
    }

    /** And two accounts of one question that disagree about that order are not put together. */
    @Test
    void twoAccountsOfOneQuestionCannotDisagreeAboutWhatTheAuthorWrote() {
        BlockReason.RuleReadingStopped form = new BlockReason.UnreadComparisonForm();
        BlockReason.RuleReadingStopped domain = new BlockReason.UnreadComparisonDomain();
        StandingQuestion one = asked(ONE_CALL, standingOn(form, domain));
        StandingQuestion theOtherWayRound =
                asked(ANOTHER_CALL, standingOn(domain, form));

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
        StandingQuestion both = asked(ONE_CALL, standingOn())
                .mergedWith(asked(ANOTHER_CALL, itsRuleAlone()));

        assertEquals(Set.of(ONE_CALL, ANOTHER_CALL), both.cited());
        assertEquals(Optional.of(new BlockReason.ExactValuesTooCostly(AT_A_FIGURE)),
                both.stopped().itsPositionWasShortOf(),
                "the question stands on it, and it was met once");
    }

    /** And two that met different limits are disagreeing about the position. */
    @Test
    void andTwoThatMetDifferentLimitsAreRefused() {
        StandingQuestion one = asked(ONE_CALL, standingOn());
        StandingQuestion other = asked(ANOTHER_CALL, new WhatAQuestionStandsOn(
                RuleReasons.one(new BlockReason.UnreadComparisonForm()),
                Optional.of(new BlockReason.RulesNotHandedOnAsSets(List.of(AT_A_FIGURE), false))));

        assertThrows(TwoAccountsOfOneQuestion.class, () -> one.mergedWith(other));
    }

    /**
     * And two that met one limit at two of its figures agree, and the question stands on that
     * limit at both.
     *
     * <p>An allowance is refused at one machine or at everything built, and which of the two a
     * reading meets turns on what was built before it — so two readings of one rule can meet one
     * limit at different figures, and neither is wrong about the position. Compared with the
     * figures in, the two were two accounts of one question that disagreed, and the model refused
     * to compile.
     */
    @Test
    void twoThatMetOneLimitAtTwoFiguresAreOneAccountMetAtBoth() {
        StandingQuestion both = asked(ONE_CALL, new WhatAQuestionStandsOn(
                RuleReasons.one(new BlockReason.PatternTooCostly(ONE_MACHINE)),
                Optional.of(new BlockReason.ExactValuesTooCostly(ONE_MACHINE))))
                .mergedWith(asked(ANOTHER_CALL, new WhatAQuestionStandsOn(
                        RuleReasons.one(new BlockReason.PatternTooCostly(AT_A_FIGURE)),
                        Optional.of(new BlockReason.ExactValuesTooCostly(AT_A_FIGURE)))));

        assertEquals(new WhatAQuestionStandsOn(
                        RuleReasons.one(new BlockReason.PatternTooCostly(
                                List.of(ONE_MACHINE, AT_A_FIGURE))),
                        Optional.of(new BlockReason.ExactValuesTooCostly(
                                List.of(ONE_MACHINE, AT_A_FIGURE)))),
                both.stopped());
    }

    /** And what one reading recorded at a position twice, at two figures, is one limit at both. */
    @Test
    void oneLimitRecordedAtTwoFiguresIsOneLimitAtBoth() {
        assertEquals(Optional.of(new BlockReason.ExactValuesTooCostly(
                        List.of(ONE_MACHINE, AT_A_FIGURE))),
                WhatAQuestionStandsOn.oneOf(List.of(
                        new BlockReason.ExactValuesTooCostly(AT_A_FIGURE),
                        new BlockReason.ExactValuesTooCostly(ONE_MACHINE))));
        assertThrows(IllegalArgumentException.class, () -> WhatAQuestionStandsOn.oneOf(List.of(
                        new BlockReason.ExactValuesTooCostly(AT_A_FIGURE),
                        new BlockReason.BehaviorDistinctionsTooCostly(AT_A_FIGURE))),
                "two limits are still two, with no order between them");
    }

    /**
     * What a rule's parts left is each reason once however many figures it was met at, and a rule
     * filed twice for one reason at two figures is one finding and one question.
     */
    @Test
    void oneReasonAtTwoFiguresIsOneEntryWhereverReasonsAreHeld() {
        RuleSite whole = RuleSite.theRuleItself();
        assertEquals(new RuleReasons(List.of(new RuleReasons.Said(whole, whole,
                        new BlockReason.PatternTooCostly(List.of(ONE_MACHINE, AT_A_FIGURE))))),
                RuleReasons.from(List.of(
                        new RuleReasons.Said(whole, whole,
                                new BlockReason.PatternTooCostly(AT_A_FIGURE)),
                        new RuleReasons.Said(whole, whole,
                                new BlockReason.PatternTooCostly(ONE_MACHINE)))));

        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        gathered.add(ONE_CALL, at("x"), new BlockReason.PatternTooCostly(ONE_MACHINE));
        gathered.add(ANOTHER_CALL, at("x"), new BlockReason.PatternTooCostly(AT_A_FIGURE));
        gathered.unclassified(ONE_CALL, List.of(), at("x"),
                new BlockReason.PatternTooCostly(ONE_MACHINE));
        gathered.unclassified(ANOTHER_CALL, List.of(), at("x"),
                new BlockReason.PatternTooCostly(AT_A_FIGURE));
        RulesWithNoLine found = gathered.found();

        BlockReason.PatternTooCostly atBoth =
                new BlockReason.PatternTooCostly(List.of(ONE_MACHINE, AT_A_FIGURE));
        assertEquals(List.of(atBoth), found.reported().stream()
                        .map(RuleWithoutALine::why).toList(),
                "one finding, met at both");
        assertEquals(List.of(atBoth), found.unclassified().stream()
                        .map(StandingQuestion.Unclassified::why).toList(),
                "one question, met at both");
        assertEquals(Set.of(ONE_CALL, ANOTHER_CALL), found.unclassified().get(0).cited());
    }

    /** What the reading of one machine was refused at. */
    private static final Figure ONE_MACHINE = WorkFigure.ADMITTED_VALUES_ONE_MACHINE.at(
            "10000 states or 50000000 looked at");

    /** The same question, met where its position's answer was worked out. */
    private static WhatAQuestionStandsOn itsRuleAlone() {
        return new WhatAQuestionStandsOn(
                RuleReasons.one(new BlockReason.UnreadComparisonForm()), Optional.empty());
    }

    /** And a question that asks something is not an account of one that asks nothing. */
    @Test
    void theTwoKindsOfStandingQuestionAreNotTwoAccountsOfOneThing() {
        StandingQuestion asks = asked(ONE_CALL, standingOn());
        StandingQuestion unclassified = StandingQuestion.NothingClassifiesIt.of(
                ONE_CALL, List.of(), at("x"), new BlockReason.UnreadComparisonForm());

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
        asFinding.add(ONE_CALL, at("x"), form);
        RulesWithNoLine.Gathered asQuestion = new RulesWithNoLine.Gathered();
        asQuestion.unclassified(ONE_CALL, List.of(), at("x"), form);

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
        gathered.add(found(ONE_CALL, "x"));

        assertEquals(null, gathered.found().aReadingThatStopped(),
                () -> "the reading got through it: " + gathered.found().reported());
    }

    private static RuleWithoutALine found(RuleCitation cited, String at) {
        return RuleWithoutALine.of(cited, at(at),
                new BlockReason.ComparisonRelatingTwoValues());
    }

    private static FilingCoordinate at(String path) {
        return new FilingCoordinate.AtPosition(TermPath.of(path));
    }

    private static StandingQuestion asked(RuleCitation cited, WhatAQuestionStandsOn stopped) {
        return StandingQuestion.Exact.of(cited,
                new InputQuestion.AboutAPosition(TermPath.of("x")), stopped);
    }

    /** One question short in both ways, which is what a fold has to keep whole. */
    private static WhatAQuestionStandsOn standingOn() {
        return new WhatAQuestionStandsOn(
                RuleReasons.one(new BlockReason.UnreadComparisonForm()),
                Optional.of(new BlockReason.ExactValuesTooCostly(AT_A_FIGURE)));
    }

    /** What an answer that ran out stopped at. */
    private static final Figure AT_A_FIGURE = WorkFigure.ADMITTED_VALUES_IN_ALL.at(
            "200000 states built and 50000000 looked at");

    /** One question short in as many ways as somebody wrote. */
    private static WhatAQuestionStandsOn standingOn(BlockReason.RuleReadingStopped... these) {
        List<RuleReasons.Said> written = new ArrayList<>();
        for (int i = 0; i < these.length; i++) {
            written.add(new RuleReasons.Said(RuleSite.at(new PartId<>(invariant(), i)),
                    RuleSite.theRuleItself(), these[i]));
        }
        return new WhatAQuestionStandsOn(RuleReasons.from(written), Optional.empty());
    }

    private static RuleRef.Comparison comparison() {
        return new RuleRef.Comparison("b", new SourceConstructOrigin(
                new WrittenOwner.Body("m", "b"), 1, 1, SourceConstruct.IF));
    }

    /** A rule the author named, for the half of the pairing that has no place. */
    private static RuleRef.Invariant invariant() {
        return new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("m", "Amount")), 0),
                Optional.of(new ClauseName("cap"))));
    }
}
