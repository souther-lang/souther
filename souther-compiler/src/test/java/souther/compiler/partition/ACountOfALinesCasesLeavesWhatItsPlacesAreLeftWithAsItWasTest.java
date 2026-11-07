package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.CaseCount;
import souther.compiler.meaning.CaseExpansion;
import souther.compiler.meaning.DecidingCase;
import souther.compiler.meaning.NumericallyConsistentWays;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Spelling;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.observe.Figure;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many ways a line's cases were is said beside why the line was not worked out, and changes
 * nothing of it: what each place of the rule is left with is the same whatever was counted, and
 * whether the count was given up past a figure of its own.
 */
class ACountOfALinesCasesLeavesWhatItsPlacesAreLeftWithAsItWasTest {

    private static final PlaceOfALine LINE = new PlaceOfALine(
            PartOfAComparison.of(WrittenLine.THE_COMPARISON), Spelling.of("x"));

    private static final ComparisonAssessment.Unread NOT_WORKED_OUT =
            new ComparisonAssessment.Unread(ComparisonAssessment.atEachOf(
                    List.of(FilingCoordinate.at(TermPath.of("x"))),
                    new BlockReason.WhereALineDecidesNotWorkedOut(new Figure.Budget(
                            CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO,
                            CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.declared()))),
                    WhereAReadingStopped.ELSEWHERE);

    private static ComparisonAssessment.Several read(List<CaseExpansion.Counted> expanded) {
        return new ComparisonAssessment.Several(List.of(new ComparisonAssessment.Several.Part(
                LINE, NOT_WORKED_OUT, List.of(), Map.of(), CasesWorkedOut.SHOWN, expanded)));
    }

    private static CaseExpansion.Counted expansion(CaseCount.Ways structural,
                                                   NumericallyConsistentWays.Counted consistent) {
        return new CaseExpansion.Counted(LINE.ofItsCases(), "g/x", "3",
                DecidingCase.alone(new Proposition.Always(true)),
                new CaseCount(structural, consistent));
    }

    @Test
    void whatEachPlaceIsLeftWithIsTheSameWhateverTheCountBesideIt() {
        BigInteger many = BigInteger.valueOf(729);
        List<List<CaseExpansion.Counted>> counts = List.of(
                List.of(expansion(new CaseCount.Ways.Exactly(many),
                        new NumericallyConsistentWays.Counted.AtMost(BigInteger.TEN))),
                List.of(expansion(new CaseCount.Ways.Exactly(many),
                        new NumericallyConsistentWays.Counted.NotCounted(
                                NumericallyConsistentWays.WhyNotCounted.STATES_A_COUNT_IS_TAKEN_IN))),
                List.of(expansion(new CaseCount.Ways.MoreThan(CaseCount.WAYS_A_COUNT_IS_HELD_TO),
                        new NumericallyConsistentWays.Counted.NotCounted(
                                NumericallyConsistentWays.WhyNotCounted.WAYS_A_COUNT_IS_HELD_TO))),
                List.of(expansion(new CaseCount.Ways.Exactly(many),
                                new NumericallyConsistentWays.Counted.AtMost(BigInteger.ONE)),
                        expansion(new CaseCount.Ways.Exactly(many),
                                new NumericallyConsistentWays.Counted.AtMost(BigInteger.TWO))));
        List<ComparisonAssessment.LeftAt> uncounted = read(List.of()).whatEachPlaceIsLeftWith();
        for (List<CaseExpansion.Counted> each : counts) {
            ComparisonAssessment.Several read = read(each);
            assertEquals(uncounted, read.whatEachPlaceIsLeftWith(),
                    "why the line was not worked out, whatever was counted beside it: " + each);
            assertEquals(each.stream().map(CaseExpansion.Counted::counted).toList(),
                    read.caseExpansions().stream().map(one -> one.cameTo().counted()).toList(),
                    "and the counts, each as it was");
        }
    }
}
