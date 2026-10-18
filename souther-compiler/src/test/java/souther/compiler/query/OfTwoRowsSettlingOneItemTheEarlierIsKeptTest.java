package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.partition.QuantityKey;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Of two rows that settle the same item, the reduction keeps the one that came first.
 *
 * <p>Which of two rows answering the same thing a person is handed is arbitrary, and the earlier
 * one keeps the block steady: the order rows are composed in is the order the searches were asked,
 * and an edit later in the model does not move what is offered above it
 * ({@link Settlements#keeping}). Held here on a table of two rows, because a model that composes
 * rows gives the order to whatever obligations it happens to owe, and a test that names the row
 * kept there is a test of those obligations and not of this.
 */
class OfTwoRowsSettlingOneItemTheEarlierIsKeptTest {

    private static final RowKey FIRST = new RowKey("f", List.of("(1, 3)"), List.of());

    private static final RowKey SECOND = new RowKey("f", List.of("(2, 5)"), List.of());

    @Test
    void theRowThatCameFirstIsTheOneKept() {
        assertEquals(Set.of(FIRST), tableOf(FIRST, SECOND, SECOND).keeping());
    }

    @Test
    void whichRowItWasComposedForDoesNotMoveIt() {
        assertEquals(Set.of(FIRST), tableOf(FIRST, SECOND, FIRST).keeping());
    }

    @Test
    void andTheOtherWayRoundTheOtherOne() {
        assertEquals(Set.of(SECOND), tableOf(SECOND, FIRST, FIRST).keeping());
    }

    /**
     * Two rows in the order given, each settling the one item, which {@code composedFor} was
     * composed for.
     */
    private static Settlements tableOf(RowKey earlier, RowKey later, RowKey composedFor) {
        ObligationIdentity item = aLine();
        SequencedMap<ObligationIdentity, RowKey> composed = new LinkedHashMap<>();
        composed.put(item, composedFor);
        SequencedMap<RowKey, Map<ObligationIdentity, Settlement>> byRow = new LinkedHashMap<>();
        byRow.put(earlier, Map.of(item, new Settlement.Settles()));
        byRow.put(later, Map.of(item, new Settlement.Settles()));
        SequencedMap<RowKey, Map<ObligationIdentity, InputOfARowForALine>> standsAt =
                new LinkedHashMap<>();
        standsAt.put(earlier, Map.of(item, standing(1, 3)));
        standsAt.put(later, Map.of(item, standing(2, 5)));
        return new Settlements(List.of(item), composed, byRow, standsAt,
                Map.of(item, standing(1, 3)));
    }

    private static InputOfARowForALine standing(int x, int y) {
        Map<NumericTerm, Place> at = new LinkedHashMap<>();
        at.put(new NumericTerm.ValueOf(TermPath.of("x")), Count.of(x));
        at.put(new NumericTerm.ValueOf(TermPath.of("y")), Count.of(y));
        return new InputOfARowForALine(TheLinesBesideABorder.aLineOverTwoPositions(), at);
    }

    private static ObligationIdentity aLine() {
        Map<NumericTerm, ExactRatio> direction = new LinkedHashMap<>();
        direction.put(new NumericTerm.ValueOf(TermPath.of("x")), ExactRatio.of(-3));
        direction.put(new NumericTerm.ValueOf(TermPath.of("y")), ExactRatio.ONE);
        return new ObligationIdentity.OfABorder(
                TheLinesBesideABorder.aLineOverTwoPositions().obligation(),
                new QuantityKey(direction));
    }
}
