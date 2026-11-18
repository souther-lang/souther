package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The helper an author is told to declare as a behavior is one every choice is written in and the
 * comparison is not, the innermost of those. Each helper list is what one construct is written in,
 * innermost first: {@code first} called inside {@code on}, as a search is in a helper a match
 * calls, and the comparison in {@code is}.
 */
class TheHelperToDeclareHoldsEveryChoiceAndNotTheComparisonTest {

    @Test
    void theInnermostHelperHoldingEveryChoiceIsNamed() {
        assertEquals(Optional.of("on"), CaseExpansion.innermostHoldingEvery(
                List.of(List.of("first", "on"), List.of("on")), List.of(List.of("is"))));
        assertEquals(Optional.of("first"), CaseExpansion.innermostHoldingEvery(
                List.of(List.of("first", "on"), List.of("first", "on")), List.of()));
    }

    @Test
    void aHelperHoldingTheComparisonAsWellIsNotNamed() {
        assertEquals(Optional.empty(), CaseExpansion.innermostHoldingEvery(
                List.of(List.of("first", "on"), List.of("on")), List.of(List.of("is", "on"))));
    }

    /** A helper cannot call a behavior, so what the call of the one named is written inside is
     *  where it has to move out of. */
    @Test
    void whatTheHelperIsCalledInsideIsSaidBesideIt() {
        assertEquals(List.of("on"), CaseExpansion.outside("first",
                List.of(List.of("first", "on"), List.of("first", "on"))));
        assertEquals(List.of(), CaseExpansion.outside("on",
                List.of(List.of("first", "on"), List.of("on"))));
    }

    @Test
    void aChoiceWrittenInNoHelperLeavesNoneToName() {
        assertEquals(Optional.empty(), CaseExpansion.innermostHoldingEvery(
                List.of(List.of("first", "on"), List.of()), List.of()));
    }

    /** A part nothing was found to have made is a choice written in no helper anyone knows of, so
     *  the helper the others are written in is not shown to hold every choice. */
    @Test
    void aPartNothingWasFoundToHaveMadeLeavesNoneToName() {
        CaseExpansion.Factor inOn = new CaseExpansion.Choice(new ModelOccurrence(
                construct(1, SourceConstruct.IF), new ExpansionLineage.Expansion(
                        ExpansionLineage.ORIGINAL, new ValueName.Helper("m", "on"),
                        new ExpansionSite.Written(construct(2, SourceConstruct.CALL)))),
                CaseExpansion.ChoiceKind.IF, 2, 1, Optional.empty());
        ModelOccurrence comparison = new ModelOccurrence(
                construct(3, SourceConstruct.BINARY), ExpansionLineage.ORIGINAL);
        assertEquals(Optional.of(new ValueName.Helper("m", "on")),
                CaseExpansion.theHelperHoldingEveryChoice(new CaseExpansion.Attributed(
                        List.of(inOn), 2, 0, List.of()), List.of(comparison))
                        .map(CaseExpansion.HelperToDeclare::helper));
        assertEquals(Optional.empty(), CaseExpansion.theHelperHoldingEveryChoice(
                new CaseExpansion.Attributed(List.of(inOn), 2, 1, List.of()),
                List.of(comparison)));
    }

    private static SourceConstructOrigin construct(int ordinal, SourceConstruct kind) {
        return SourceConstructOrigin.written(new WrittenOwner.Body("m", "f"), ordinal, kind);
    }
}
