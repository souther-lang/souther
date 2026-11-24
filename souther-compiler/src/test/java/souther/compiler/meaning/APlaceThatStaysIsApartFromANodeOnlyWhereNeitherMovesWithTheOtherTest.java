package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A place that stays put is apart from the node a statement is moved over only where neither stands
 * at, under or around the other as the value is reached ({@link WrittenOfANode#apart}): a narrowing
 * to a case is no step into the value, so the container a node narrowed to a case is inside holds
 * that node; and a place under another case of a value the node is in does not move with it.
 */
class APlaceThatStaysIsApartFromANodeOnlyWhereNeitherMovesWithTheOtherTest {

    private static final TermPath R = TermPath.of("r");
    private static final TermPath PRESENT = R.refine(Refinement.of(new Case.Presence(true)));
    private static final TermPath ABSENT = R.refine(Refinement.of(new Case.Presence(false)));

    @Test
    void theContainerOfANodeNarrowedToACaseHoldsTheNode() {
        assertFalse(WrittenOfANode.apart(R.then("items"), PRESENT.then("items").element()));
        assertFalse(WrittenOfANode.apart(PRESENT.then("items"), R.then("items").element()));
        assertFalse(WrittenOfANode.apart(R, PRESENT.then("items").element()));
    }

    @Test
    void aFieldBesideANodeNarrowedToACaseIsApartFromIt() {
        assertTrue(WrittenOfANode.apart(R.then("total"), PRESENT.then("items").element()));
        assertTrue(WrittenOfANode.apart(PRESENT.then("total"), R.then("items").element()));
    }

    @Test
    void aPlaceUnderAnotherCaseOfTheValueTheNodeIsInIsApartFromIt() {
        assertTrue(WrittenOfANode.apart(ABSENT.then("items"), PRESENT.then("items").element()));
    }
}
