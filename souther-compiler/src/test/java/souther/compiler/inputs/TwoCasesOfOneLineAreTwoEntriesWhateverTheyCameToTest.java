package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.meaning.CaseCount;
import souther.compiler.meaning.CaseExpansion;
import souther.compiler.meaning.NumericallyConsistentWays;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Spelling;
import souther.compiler.meaning.WrittenChoice;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.math.BigInteger;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a rule's line was told of its cases is kept one entry per case, as the reading told the
 * cases apart, and by nothing else: two cases of one line that came to the same are two entries,
 * and one case is one entry whatever its readings came to — each reading an answer at the copies
 * it was read at, and one copy answering one way.
 */
class TwoCasesOfOneLineAreTwoEntriesWhateverTheyCameToTest {

    private static final RuleCitation CITED = new RuleCitation.Written(
            new RuleRef.Comparison("g", new SourceConstructOrigin(
                    new WrittenOwner.Body("m", "g"), 1, 1, SourceConstruct.IF)),
            new RuleReportAnchor.ByTheReadingThatMetIt("Main", "g", 0));

    private static final CaseCount COUNTED = new CaseCount(
            new CaseCount.Ways.Exactly(BigInteger.valueOf(300)),
            new NumericallyConsistentWays.Counted.AtMost(BigInteger.valueOf(20)));

    /** The first arm of an {@code if} the author wrote in {@code g}. */
    private static final WrittenLine AN_ARM = new WrittenLine(List.of(new WrittenLine.Arm(
            new WrittenChoice(new SourceConstructOrigin(new WrittenOwner.Body("m", "g"), 2, 2,
                    SourceConstruct.IF), List.of()), 0, false)));

    /** A construct of the model in {@code g}, the {@code ordinal}th. */
    private static ModelOccurrence construct(int ordinal, SourceConstruct kind) {
        return new ModelOccurrence(new SourceConstructOrigin(new WrittenOwner.Body("m", "g"),
                ordinal, 0, kind), ExpansionLineage.ORIGINAL);
    }

    /** Two copies the rule could be read at. */
    private static final ModelOccurrences ONE_COPY =
            ModelOccurrences.of(construct(10, SourceConstruct.BINARY));
    private static final ModelOccurrences ANOTHER_COPY =
            ModelOccurrences.of(construct(11, SourceConstruct.BINARY));

    /** What the case came to where the {@code if} at {@code ordinal} made its parts. */
    private static CaseExpansion.CameTo madeByTheIfAt(int ordinal) {
        return new CaseExpansion.CameTo(COUNTED, new CaseExpansion.Attributed(List.of(
                new CaseExpansion.Choice(construct(ordinal, SourceConstruct.IF),
                        CaseExpansion.ChoiceKind.IF, 2, 4, Optional.empty())), 4, 0), List.of());
    }

    private static final CaseExpansion.CameTo NOTHING_NAMED = new CaseExpansion.CameTo(COUNTED,
            new CaseExpansion.Attributed(List.of(), 4, 4), List.of());

    private static CaseExpansion ofTheCase(Proposition condition) {
        return ofTheCase(WrittenLine.THE_COMPARISON, condition, NOTHING_NAMED);
    }

    private static CaseExpansion ofTheCase(WrittenLine written, Proposition condition,
                                           CaseExpansion.CameTo cameTo) {
        return new CaseExpansion(new CaseExpansion.Which(
                new CaseExpansion.Line(written, Spelling.of("x")), condition), "g/x", "3", cameTo);
    }

    private record Told(ModelOccurrences at, CaseExpansion expansion) {}

    private static List<CasesExpandedAtARule> gathered(Told... told) {
        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        for (Told each : told) {
            gathered.expanded(CITED, each.at(), each.expansion());
        }
        return gathered.found().expanded();
    }

    @Test
    void twoCasesComingToTheSameAreTwoEntries() {
        assertEquals(2, gathered(new Told(ONE_COPY, ofTheCase(new Proposition.Always(true))),
                new Told(ONE_COPY, ofTheCase(new Proposition.Always(false)))).size(),
                "one entry for each case the reading told apart");
    }

    /** Two of the author's lines coming to one relation are two places, and their cases two. */
    @Test
    void twoLinesTheAuthorWroteComingToOneRelationAreTwoEntries() {
        assertEquals(2, gathered(
                new Told(ONE_COPY, ofTheCase(WrittenLine.THE_COMPARISON,
                        new Proposition.Always(true), NOTHING_NAMED)),
                new Told(ONE_COPY, ofTheCase(AN_ARM, new Proposition.Always(true),
                        NOTHING_NAMED))).size(),
                "the same relation and condition, of two lines the author wrote");
    }

    @Test
    void oneCaseToldTwiceIsOneEntry() {
        List<CasesExpandedAtARule> told = gathered(
                new Told(ONE_COPY, ofTheCase(new Proposition.Always(true))),
                new Told(ONE_COPY, ofTheCase(new Proposition.Always(true))));
        assertEquals(1, told.size(), "the same case of the same line, told by two readers");
        assertEquals(1, told.getFirst().readings().size(), "and the same answer, once");
    }

    /**
     * One case read at two copies of the rule, each naming what made its parts there, is one
     * entry with two readings — never two cases.
     */
    @Test
    void oneCaseReadAtTwoCopiesIsOneEntryWithAnAnswerAtEach() {
        Proposition condition = new Proposition.Always(true);
        List<CasesExpandedAtARule> told = gathered(
                new Told(ONE_COPY, ofTheCase(WrittenLine.THE_COMPARISON, condition,
                        madeByTheIfAt(3))),
                new Told(ANOTHER_COPY, ofTheCase(WrittenLine.THE_COMPARISON, condition,
                        madeByTheIfAt(4))));
        assertEquals(1, told.size(), "one case, whatever its readings came to");
        assertEquals(List.of(new CasesExpandedAtARule.Reading(ONE_COPY, madeByTheIfAt(3)),
                        new CasesExpandedAtARule.Reading(ANOTHER_COPY, madeByTheIfAt(4))),
                told.getFirst().readings(), "an answer for each copy, at that copy");
    }

    /** Copies whose readings came to the same are one reading, read at both. */
    @Test
    void readingsThatCameToTheSameAreOneReadAtEachOfTheirCopies() {
        Proposition condition = new Proposition.Always(true);
        List<CasesExpandedAtARule> told = gathered(
                new Told(ONE_COPY, ofTheCase(WrittenLine.THE_COMPARISON, condition,
                        madeByTheIfAt(3))),
                new Told(ANOTHER_COPY, ofTheCase(WrittenLine.THE_COMPARISON, condition,
                        madeByTheIfAt(3))));
        assertEquals(List.of(new CasesExpandedAtARule.Reading(ONE_COPY.and(ANOTHER_COPY),
                madeByTheIfAt(3))), told.getFirst().readings());
    }

    /** One copy reads a case once, so one answering it two ways is two answers disagreeing. */
    @Test
    void oneCopyAnsweringOneCaseTwoWaysIsRaised() {
        Proposition condition = new Proposition.Always(true);
        assertThrows(IllegalStateException.class, () -> gathered(
                new Told(ONE_COPY, ofTheCase(WrittenLine.THE_COMPARISON, condition,
                        madeByTheIfAt(3))),
                new Told(ONE_COPY, ofTheCase(WrittenLine.THE_COMPARISON, condition,
                        madeByTheIfAt(4)))));
    }
}
