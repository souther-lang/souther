package souther.compiler.coverage;

import souther.compiler.query.WeakeningSet;
import org.junit.jupiter.api.Test;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.types.CoverageConstruct;
import souther.compiler.types.CoverageOrigin;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An obligation nothing settled is uncertain however many places it was counted at.
 *
 * <p>What an unsettled rule leaves undecided is how many rules the obligation stands for, and one
 * place can stand for several: a rule chosen while the behavior runs arrives at one call site, and
 * the arms one of them takes say nothing about the arms another would. Asked as "were several
 * places put together", such a place came back settled — its arms were judged as though one rule
 * had been through them, and the count called itself complete over two.
 *
 * <p>Built here rather than compiled from a model. A model whose rule is chosen while it runs is
 * written in this language and is the case this is about, but its rows cannot be read at all -- the
 * arms come back unavailable, so nothing downstream of them is reached. What this holds is the rule
 * the reading follows on the day they can be, and
 * {@code ARuleChosenWhileItRunsIsNeverACompleteMeasureTest} holds the end of it that a model can
 * reach today.
 */
class AnUnsettledDecisionIsUncertainHoweverManyPlacesItHasTest {

    private static final CoverageOrigin FORK =
            CoverageOrigin.written("m", 0, CoverageConstruct.IF);

    private static CoverageSites.Site arm(int index, DecidedBy decided) {
        return new CoverageSites.Site("b",
                new SourceOutcome.Held(new SourceOutcome.HeldBy.Condition()), null, index, index,
                new CoverageSites.Obligation("b", FORK, index, decided));
    }

    /** Two arms of one fork, neither of them reached. */
    private static Adequacy.BranchEvidence over(DecidedBy decided) {
        return Adequacy.BranchEvidence.measured("b",
                List.of(arm(0, decided), arm(1, decided)), Set.of(),
                souther.compiler.query.Adequacy.NOTHING_PROVEN, WeakeningSet.none());
    }

    /** One place whose rule nothing settled is a fork this cannot say how many rules it stands for. */
    @Test
    void onePlaceNothingSettledIsSaidToBeUncertain() {
        assertEquals(List.of(FORK), over(DecidedBy.NOT_SAID).unsettledDecisions(),
                "however many places it was counted at");
    }

    /** And its arms are not judged, so nothing is owed a row over a rule that may not be one. */
    @Test
    void andItsArmsAreNotJudged() {
        assertEquals(List.of(), over(DecidedBy.NOT_SAID).unreached().stream()
                        .map(each -> each.name().toString()).toList(),
                "a row through one of them may or may not be a row through this obligation");
    }

    /** Which is only worth saying beside what a settled one comes to over the same arms. */
    @Test
    void whileASettledOnesArmsAreOwedARow() {
        assertEquals(2, over(DecidedBy.THE_DECLARATION).unreached().size(),
                "both arms of it, and no row goes through either");
    }

    /** A settled one is read like any other. */
    @Test
    void aSettledOneIsReadLikeAnyOther() {
        assertEquals(List.of(), over(DecidedBy.THE_DECLARATION).unsettledDecisions(),
                "nothing about it is in doubt");
    }
}
