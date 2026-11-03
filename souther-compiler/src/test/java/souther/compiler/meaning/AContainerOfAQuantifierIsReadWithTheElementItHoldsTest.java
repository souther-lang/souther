package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A quantifier names a container as well as the statement it makes of an element, and the
 * container is a place the statement reads. Reading the parts it holds is not reading the
 * container.
 */
class AContainerOfAQuantifierIsReadWithTheElementItHoldsTest {

    private static final TermPath NODE = TermPath.of("o").then("node");
    private static final TermPath KIDS = NODE.then("kids");
    private static final TermPath ELSEWHERE = TermPath.of("o").then("other");

    private static final Proposition KID_HOLDS =
            new Proposition.Truth(new DecisionSubject.AnInput(KIDS.then("flag")), true);

    private static Proposition.Some some(TermPath container) {
        return new Proposition.Some(new DecisionSubject.AnInput(container), KID_HOLDS, true);
    }

    @Test
    void aContainerUnderTheNodeIsReadOfTheNode() {
        assertTrue(WrittenOfANode.movesWithIt(some(KIDS), NODE, List.of()));
    }

    @Test
    void aContainerOutsideTheNodeKeepsTheQuantifierFromBeingReadOfIt() {
        assertFalse(WrittenOfANode.movesWithIt(some(ELSEWHERE), NODE, List.of()));
    }

    @Test
    void theNodesReachableAreNeverReadOfTheNode() {
        Proposition reached = new Proposition.SomeReachable(
                NODE, NODE, List.of("next"), KID_HOLDS, Optional.empty(), true);
        assertFalse(WrittenOfANode.movesWithIt(reached, NODE, List.of()));
        assertFalse(WrittenOfANode.movesWithIt(
                new Proposition.All(List.of(KID_HOLDS, reached)), NODE, List.of()));
    }

    @Test
    void theContainerIsAPlaceTheStatementReadsBeforeTheElementIs() {
        Proposition.Some quantified = some(KIDS);
        assertEquals(Optional.of(List.of(KIDS, KIDS.then("flag"))),
                PositionsAStatementReads.everyPlaceOf(quantified));
        Proposition note = new Proposition.Truth(new DecisionSubject.AnInput(NODE.then("note")), true);
        assertEquals(Optional.of(List.of(KIDS, KIDS.then("flag"), NODE.then("note"))),
                PositionsAStatementReads.everyPlaceOf(
                        new Proposition.All(List.of(quantified, note))));
    }
}
