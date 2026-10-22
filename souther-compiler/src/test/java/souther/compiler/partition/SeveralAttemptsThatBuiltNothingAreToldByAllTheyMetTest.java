package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Attempts at one container stop for different reasons, and what a composing that built nothing
 * is told as is every one of them and not the last: a figure that cut an attempt short is
 * somebody's to raise whatever a later attempt came to.
 */
class SeveralAttemptsThatBuiltNothingAreToldByAllTheyMetTest {

    private static final CompositionBudget FIGURE = CompositionBudget.ELEMENTS_A_TOTAL_IS_SPREAD_OVER;

    private static TermRealizations.Realization stopped() {
        return new TermRealizations.Realization.Stopped(CompositionShortfall.of(Set.of(FIGURE)));
    }

    private static TermRealizations.Realization someOfThem() {
        return new TermRealizations.Realization.Unexhausted(CompositionShortfall.writing(
                Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD)), "walked some");
    }

    private static TermRealizations.Realization nothing() {
        return new TermRealizations.Realization.None(
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, "nothing");
    }

    @Test
    void aFigureAnAttemptMetIsKeptWhateverALaterAttemptCameTo() {
        for (TermRealizations.Realization later : List.of(someOfThem(), nothing())) {
            UnbuiltAttempts attempts = new UnbuiltAttempts();
            attempts.add(stopped());
            attempts.add(later);

            TermRealizations.Realization came = attempts.came(CompositionShortfall.NONE, nothing());

            TermRealizations.Realization.Stopped told =
                    assertInstanceOf(TermRealizations.Realization.Stopped.class, came);
            assertEquals(Set.of(FIGURE), told.met().figures());
        }
    }

    @Test
    void whatEveryAttemptSawOfTheRepertoireIsJoinedWithTheFigures() {
        UnbuiltAttempts attempts = new UnbuiltAttempts();
        attempts.add(someOfThem());
        attempts.add(stopped());

        TermRealizations.Realization.Stopped told = assertInstanceOf(
                TermRealizations.Realization.Stopped.class,
                attempts.came(CompositionShortfall.NONE, nothing()));

        assertEquals(CompositionShortfall.of(Set.of(FIGURE))
                .and(CompositionShortfall.writing(
                        Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD))), told.met());
    }

    @Test
    void aWalkThatSawSomeIsNotToldAsOneThatSawNone() {
        UnbuiltAttempts attempts = new UnbuiltAttempts();
        attempts.add(someOfThem());
        attempts.add(nothing());

        TermRealizations.Realization.Unexhausted told = assertInstanceOf(
                TermRealizations.Realization.Unexhausted.class,
                attempts.came(CompositionShortfall.NONE, nothing()));

        assertEquals("walked some", told.detail());
    }

    @Test
    void whatTheComposingMetBesidesTheAttemptsIsJoinedWithWhatTheyMet() {
        UnbuiltAttempts attempts = new UnbuiltAttempts();
        attempts.add(nothing());

        assertInstanceOf(TermRealizations.Realization.Stopped.class,
                attempts.came(CompositionShortfall.of(Set.of(FIGURE)), nothing()));
    }

    @Test
    void attemptsThatFoundNothingAreToldAsTheLastFoundItAndNoAttemptAsWhatIsSaidInstead() {
        UnbuiltAttempts attempts = new UnbuiltAttempts();
        TermRealizations.Realization instead = nothing();
        assertEquals(instead, attempts.came(CompositionShortfall.NONE, instead));

        TermRealizations.Realization last = nothing();
        attempts.add(nothing());
        attempts.add(last);
        assertEquals(last, attempts.came(CompositionShortfall.NONE, instead));
    }

    @Test
    void anAttemptThatBuiltSomethingIsNotOneThatBuiltNothing() {
        assertThrows(IllegalArgumentException.class, () -> new UnbuiltAttempts().add(
                new TermRealizations.Realization.Built(List.of(), CompositionShortfall.NONE)));
    }

    /** The keys' counts are tried one combination at a time and every one that fails is told. */
    @Test
    void aStopOfAnEarlierCombinationOfKeysIsKeptWhenALaterOneFindsNothing() {
        AtomicInteger calls = new AtomicInteger();
        List<Place> values = List.of(Count.of(1));
        List<List<NumericSet>> wanted = List.of(List.of(new NumericSet.At(Count.of(1))));
        CardinalityComposer.ValuesCountedFor search = new CardinalityComposer.ValuesCountedFor(
                values, wanted, NumericDomain.Bounds.OPEN,
                List.of(Count.of(100), Count.of(101)), (counted, others) ->
                        calls.getAndIncrement() == 0 ? stopped() : nothing());

        search.counting(0, new ArrayList<>(), 0);

        assertTrue(calls.get() > 1, "more than one container was tried");
        assertInstanceOf(TermRealizations.Realization.Stopped.class,
                search.unbuilt.came(CompositionShortfall.NONE, nothing()));
    }
}
