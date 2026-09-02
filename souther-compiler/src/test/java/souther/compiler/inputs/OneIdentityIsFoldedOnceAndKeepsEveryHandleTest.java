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
 * The readers that find a rule with no line put their findings together in one place, and it keeps
 * every handle.
 *
 * <p>Six readers gathered these, and each did it by walking what it already had and keeping the
 * first where it matched. So a rule found by two readers came out cited whichever way was met
 * first, and a fold further down that accumulated could only accumulate what these let through —
 * which is what made the claim that nothing depends on the readers agreeing untrue one level up
 * from where it was made.
 *
 * <p>What is asked here is the fold itself, because that is what those six became. Asked of what
 * the fold produces and not of a report, so that it says something about a rule found twice
 * whether or not this compiler's readers do that today.
 */
class OneIdentityIsFoldedOnceAndKeepsEveryHandleTest {

    private static final RuleCitation NAMED = new RuleCitation.Named("n");
    private static final RuleCitation PLACED =
            new RuleCitation.WrittenAt(Citation.of(new SourcePos(3, 3)));

    @Test
    void oneRuleFoundTwiceIsOneFindingCitedBothWays() {
        RuleWithoutALine.Gathered gathered = new RuleWithoutALine.Gathered();
        gathered.add(found(NAMED, "x"));
        gathered.add(found(PLACED, "x"));

        assertEquals(1, gathered.all().size(),
                () -> "one rule at one position for one reason is one finding: " + gathered.all());
        assertEquals(Set.of(NAMED, PLACED), gathered.all().get(0).cited(),
                "and a reader can be sent to it either way either reader offered");
    }

    /** Which of the two was found first decides nothing about what comes out. */
    @Test
    void whichReaderFoundItFirstDecidesNothing() {
        RuleWithoutALine.Gathered one = new RuleWithoutALine.Gathered();
        one.add(found(NAMED, "x"));
        one.add(found(PLACED, "x"));
        RuleWithoutALine.Gathered theOtherWayRound = new RuleWithoutALine.Gathered();
        theOtherWayRound.add(found(PLACED, "x"));
        theOtherWayRound.add(found(NAMED, "x"));

        assertEquals(one.all(), theOtherWayRound.all());
    }

    /** And two rules are two findings, so the fold is on the rule and not on everything at once. */
    @Test
    void twoRulesAreTwoFindings() {
        RuleWithoutALine.Gathered gathered = new RuleWithoutALine.Gathered();
        gathered.add(found(NAMED, "x"));
        gathered.add(found(NAMED, "y"));

        assertEquals(2, gathered.all().size(), () -> gathered.all().toString());
    }

    /** And nothing puts together two findings that are not one rule. */
    @Test
    void twoFindingsThatAreNotOneRuleAreNotPutTogether() {
        RuleWithoutALine here = found(NAMED, "x");
        RuleWithoutALine elsewhere = found(NAMED, "y");

        assertThrows(IllegalArgumentException.class, () -> here.mergedWith(elsewhere));
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

    private static RuleWithoutALine found(RuleCitation cited, String at) {
        return RuleWithoutALine.of(comparison(), cited,
                new FilingCoordinate.AtPosition(TermPath.of(at)),
                new BlockReason.UnreadComparisonForm());
    }

    private static StandingQuestion asked(RuleCitation cited,
                                          List<BlockReason.AboutARule> stopped) {
        return StandingQuestion.of(comparison(), cited,
                new InputQuestion.AboutAPosition(TermPath.of("x")), stopped);
    }

    private static RuleRef comparison() {
        return new RuleRef.Comparison("b", new CoverageOrigin("m", 1, 1, CoverageConstruct.IF));
    }
}
