package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

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
}
