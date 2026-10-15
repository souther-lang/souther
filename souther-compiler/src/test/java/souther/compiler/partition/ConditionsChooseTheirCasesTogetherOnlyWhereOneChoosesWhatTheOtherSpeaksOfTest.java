package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Conditions about names the cases of a sum share are chosen together where one chooses a case of
 * a sum the other speaks of, and apart where all they share is a case both stand under alike.
 *
 * <p>Built on requirements made here: an optional's two carriers stand in for a sum's cases, which
 * is all the grouping reads. {@code outer} is a value both conditions stand under the {@code X} case
 * of, and {@code s1} and {@code s2} are two sums inside it.
 */
class ConditionsChooseTheirCasesTogetherOnlyWhereOneChoosesWhatTheOtherSpeaksOfTest {

    private static final Refinement ONE = Refinement.of(new Case.Presence(true));
    private static final Refinement OTHER = Refinement.of(new Case.Presence(false));
    private static final TermPath OUTER = TermPath.of("outer");

    /** A condition on {@code flag} under {@code sum}, under the {@code X} case of {@code outer}: one
     *  requirement per case of {@code sum}. */
    private static List<Requirements> onAFlagOf(String sum, Refinement outerIs) {
        TermPath at = OUTER.refine(outerIs).then(sum);
        return List.of(at.refine(ONE).then("flag").requirements(),
                at.refine(OTHER).then("flag").requirements());
    }

    @Test
    void twoConditionsOnOneSumChooseTogether() {
        assertEquals(List.of(List.of(0, 1)), CaseChoices.chosenTogether(
                List.of(onAFlagOf("s1", ONE), onAFlagOf("s1", ONE))));
    }

    /** A sum inside one case of another is chosen with it: its cases are under that case. */
    @Test
    void aSumInsideACaseOfAnotherIsChosenWithIt() {
        TermPath inner = OUTER.refine(ONE).then("s1").refine(ONE).then("inner");
        List<Requirements> underInner = List.of(inner.refine(ONE).then("flag").requirements(),
                inner.refine(OTHER).then("flag").requirements());
        assertEquals(List.of(List.of(0, 1)), CaseChoices.chosenTogether(
                List.of(onAFlagOf("s1", ONE), underInner)));
    }

    /**
     * Two sums inside the one case both stand under are chosen apart: the case of {@code outer} is
     * the same for both and chosen by neither, so each choice is its own.
     */
    @Test
    void twoSumsUnderACaseBothStandUnderAreChosenApart() {
        assertEquals(List.of(List.of(0), List.of(1), List.of(2)), CaseChoices.chosenTogether(
                List.of(onAFlagOf("s1", ONE), onAFlagOf("s2", ONE), onAFlagOf("s3", ONE))));
    }

    @Test
    void sumsNothingRelatesAreChosenApart() {
        TermPath other = TermPath.of("other");
        List<Requirements> elsewhere = List.of(other.refine(ONE).then("flag").requirements(),
                other.refine(OTHER).then("flag").requirements());
        assertEquals(List.of(List.of(0), List.of(1)), CaseChoices.chosenTogether(
                List.of(onAFlagOf("s1", ONE), elsewhere)));
    }

    /** What both take as given about one sum, where it differs, has to be met by one row. */
    @Test
    void twoConditionsTakingASumDifferentlyAreChosenTogether() {
        assertEquals(List.of(List.of(0, 1)), CaseChoices.chosenTogether(
                List.of(onAFlagOf("s1", ONE), onAFlagOf("s2", OTHER))));
    }
}
