package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row is asked a compound statement through the parts it holds only for the compounds that say
 * what they hold by those parts. A statement over the nodes reachable from one, or over each of
 * the applications of something, is not asked through the parts it holds, whatever each of them
 * would be asked alone.
 */
class AStatementARowIsAskedOnlyThroughTheCompoundsItNamesTest {

    private static final TermPath OPEN = TermPath.of("o").then("open");
    private static final TermPath NODE = TermPath.of("o").then("node");
    private static final TermPath FLAG = TermPath.of("o").then("node").then("flag");

    private static final Proposition OPEN_HOLDS =
            new Proposition.Truth(new DecisionSubject.AnInput(OPEN), true);
    private static final Proposition FLAG_HOLDS =
            new Proposition.Truth(new DecisionSubject.AnInput(FLAG), true);

    private static final Proposition SOME_NODE_REACHED = new Proposition.SomeReachable(
            NODE, NODE, List.of("next"), FLAG_HOLDS, Optional.empty(), true);
    private static final Proposition ON_EACH_APPLICATION =
            new Proposition.OnAnApplication(List.of(OPEN_HOLDS, FLAG_HOLDS), null);

    @Test
    void thePartsOfACompoundItNamesAreAskedOneByOne() {
        assertTrue(AStatementAtARow.askable(new Proposition.All(List.of(OPEN_HOLDS, FLAG_HOLDS))));
        assertTrue(AStatementAtARow.askable(new Proposition.Any(List.of(OPEN_HOLDS, FLAG_HOLDS))));
    }

    @Test
    void aPartThatIsNotAskedKeepsTheWholeFromBeingAsked() {
        assertFalse(AStatementAtARow.askable(
                new Proposition.All(List.of(OPEN_HOLDS, SOME_NODE_REACHED))));
        assertFalse(AStatementAtARow.askable(
                new Proposition.Any(List.of(SOME_NODE_REACHED, OPEN_HOLDS))));
    }

    @Test
    void aStatementOverTheNodesReachableIsNotAskedForItsPartBeingAsked() {
        assertTrue(AStatementAtARow.askable(FLAG_HOLDS));
        assertFalse(AStatementAtARow.askable(SOME_NODE_REACHED));
    }

    @Test
    void aStatementOverEachApplicationIsNotAskedForItsPartBeingAsked() {
        assertTrue(AStatementAtARow.askable(OPEN_HOLDS));
        assertFalse(AStatementAtARow.askable(ON_EACH_APPLICATION));
    }
}
