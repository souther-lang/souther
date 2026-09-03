package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.CoverageConstruct;
import souther.compiler.types.CoverageOrigin;

import java.util.List;
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
        List<BlockReason.AboutARule> stopped = List.of(new BlockReason.UnreadComparisonForm(),
                new BlockReason.NoReadingTookItIn());

        StandingQuestion both = asked(NAMED, stopped).mergedWith(asked(PLACED, stopped));

        assertEquals(Set.of(NAMED, PLACED), both.cited());
        assertEquals(stopped, both.stopped());
    }

    /** And two accounts of one question that disagree about that order are not put together. */
    @Test
    void twoAccountsOfOneQuestionCannotDisagreeAboutWhatTheAuthorWrote() {
        BlockReason.AboutARule form = new BlockReason.UnreadComparisonForm();
        BlockReason.AboutARule none = new BlockReason.NoReadingTookItIn();
        StandingQuestion one = asked(NAMED, List.of(form, none));
        StandingQuestion theOtherWayRound = asked(PLACED, List.of(none, form));

        assertThrows(IllegalArgumentException.class, () -> one.mergedWith(theOtherWayRound));
    }

    /** And a question that asks something is not an account of one that asks nothing. */
    @Test
    void theTwoKindsOfStandingQuestionAreNotTwoAccountsOfOneThing() {
        StandingQuestion asks = asked(NAMED, List.of(new BlockReason.UnreadComparisonForm()));
        StandingQuestion unclassified = StandingQuestion.NothingClassifiesIt.of(
                comparison(), NAMED, at("x"), new BlockReason.UnreadComparisonForm());

        assertThrows(IllegalArgumentException.class, () -> asks.mergedWith(unclassified));
        assertThrows(IllegalArgumentException.class, () -> unclassified.mergedWith(asks));
    }

    private static RuleWithoutALine found(RuleCitation cited, String at) {
        return RuleWithoutALine.of(comparison(), cited, at(at),
                new BlockReason.ComparisonBetweenPositions());
    }

    private static FilingCoordinate at(String path) {
        return new FilingCoordinate.AtPosition(TermPath.of(path));
    }

    private static StandingQuestion asked(RuleCitation cited,
                                          List<BlockReason.AboutARule> stopped) {
        return StandingQuestion.Exact.of(comparison(), cited,
                new InputQuestion.AboutAPosition(TermPath.of("x")), stopped);
    }

    private static RuleRef comparison() {
        return new RuleRef.Comparison("b", new CoverageOrigin("m", 1, 1, CoverageConstruct.IF));
    }
}
