package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A stop turns on a place when it reads the place, and also when whether a run works it out at
 * all does: the containers the closure around it is applied over, and what decides whether they
 * hold anything — the key of a lookup. A row that got past the stop by not working it out gets
 * past another value of the place only where that value leaves it not worked out.
 */
class AStopTurnsOnWhatDecidesWhetherItIsWorkedOutAsOnWhatItReadsTest {

    private static final TermPath CURRENCY = TermPath.of("currency");
    private static final TermPath AMOUNT = TermPath.of("amount");
    private static final TermPath RATES = TermPath.of("rates");

    private static Pullback.WorkedOutWhere inside(Set<TermPath> containers,
                                                  Set<TermPath> decidedBy) {
        return new Pullback.WorkedOutWhere(List.of(containers), decidedBy, true);
    }

    @Test
    void aStopWorkedOutOnEveryRunTurnsOnlyOnWhatItReads() {
        assertFalse(UndividedByARelation.stopTurnsOn(CURRENCY, Set.of(AMOUNT),
                Pullback.WorkedOutWhere.ALWAYS));
        assertTrue(UndividedByARelation.stopTurnsOn(CURRENCY, Set.of(CURRENCY, AMOUNT),
                Pullback.WorkedOutWhere.ALWAYS));
    }

    @Test
    void aStopTurnsOnTheContainersItIsWorkedOutInside() {
        assertTrue(UndividedByARelation.stopTurnsOn(RATES, Set.of(AMOUNT),
                inside(Set.of(RATES), Set.of())));
        assertFalse(UndividedByARelation.stopTurnsOn(CURRENCY, Set.of(AMOUNT),
                inside(Set.of(RATES), Set.of())));
    }

    @Test
    void aStopTurnsOnTheKeyOfTheLookupThatDecidesWhetherItIsWorkedOut() {
        assertTrue(UndividedByARelation.stopTurnsOn(CURRENCY, Set.of(AMOUNT),
                inside(Set.of(RATES), Set.of(RATES, CURRENCY))));
    }

    @Test
    void aStopInsideWhatIsNotSaidTurnsOnAnyPlace() {
        assertTrue(UndividedByARelation.stopTurnsOn(CURRENCY, Set.of(AMOUNT),
                Pullback.WorkedOutWhere.ALWAYS.notSaid()));
    }
}
