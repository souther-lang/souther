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
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The input a report names for a line is the input of the row a person is handed, and not the one
 * a search composed at.
 *
 * <p>Which row that is has two rules, and they are the two halves of {@link Settlements#offers}: a
 * row that tells the two lines apart answers the line whoever it was composed for, and the row
 * composed <em>for</em> the line is what a person was offered for it whether or not this walk can
 * tell that it settles it. So the reduction may drop the row composed for the line — another row
 * already offers for it — and may keep one whose reading came back undetermined.
 *
 * <p><b>And a row shown to settle the line is shown before one that is only composed for it.</b>
 * Which row a line was composed for is how the row came to be asked for, not what it was read back
 * to do; a row kept for another item that does not rule the line out is no input to name for it
 * while a row that does is handed over beside it.
 *
 * <p><b>Each half knows the input a different way.</b> The row composed for the line was built from
 * what the realizer asked for; a row that settles it was read against the line, and what it holds
 * there is what that reading came to. A walk that took the input from the reading alone had nothing
 * to name for the rows the second half keeps, and a report fell back to what the measurement saw
 * while the block handed over the other place.
 *
 * <p>Held at the table rather than over a model. What has to be true is a rule about which row
 * answers an item once the reduction has run, and a model in which a row composed for something
 * else happens to fall between two lines is a long way round to asking it.
 */
class TheInputShownForALineIsTheOneTheOfferedRowStandsAtTest {

    private static final ObligationIdentity LINE = aLine();

    private static final RowKey COMPOSED_FOR_IT = new RowKey("f", List.of("(1, 3)"), List.of());

    private static final RowKey COMPOSED_FOR_SOMETHING_ELSE =
            new RowKey("f", List.of("(2, 5)"), List.of());

    @Test
    void theRowComposedForTheLineNamesItWhileTheReductionKeepsIt() {
        Settlements table = bothSettleIt();

        assertEquals("x = 1, y = 3",
                table.shownFor(Set.of(COMPOSED_FOR_IT, COMPOSED_FOR_SOMETHING_ELSE))
                        .get(LINE).at().orElseThrow().said(),
                "the row composed for the line is the one a person is handed for it");
    }

    @Test
    void andTheRowThatIsLeftNamesItOnceTheReductionHasDroppedThatOne() {
        Settlements table = bothSettleIt();

        assertEquals("x = 2, y = 5",
                table.shownFor(Set.of(COMPOSED_FOR_SOMETHING_ELSE)).get(LINE).at().orElseThrow().said(),
                "a row composed for something else answers the line as much, so when the row"
                        + " composed for it goes the input shown is where that one was read");
    }

    /**
     * A row nothing could read back is offered like any other, and the input shown is the one it
     * was composed at.
     *
     * <p>Which is the half a reading cannot answer. The search composed the row and what placed it
     * never came back, so the table says nothing about where it stands — and it is still the one
     * piece of work anybody was handed for this line.
     */
    @Test
    void aRowNothingCouldReadBackIsShownTheInputItWasComposedAt() {
        SequencedMap<ObligationIdentity, RowKey> composedFor = new LinkedHashMap<>();
        composedFor.put(LINE, COMPOSED_FOR_IT);
        SequencedMap<RowKey, Map<ObligationIdentity, Settlement>> byRow = new LinkedHashMap<>();
        byRow.put(COMPOSED_FOR_IT, Map.of(LINE,
                new Settlement.Undetermined(Settlement.Reason.NO_ACCOUNT_OF_THE_RUN)));
        Settlements table = new Settlements(List.of(LINE), composedFor, byRow,
                new LinkedHashMap<>(), Map.of(LINE, standing(1, 3)));

        assertEquals("x = 1, y = 3", table.shownFor(Set.of(COMPOSED_FOR_IT)).get(LINE).at().orElseThrow().said(),
                "the row is offered for the line, so the input shown is the one it was composed"
                        + " at — a reading that did not happen names nowhere");
    }

    /**
     * The row composed for the line, kept for another item and not ruling the line out, is not what
     * the line is shown at while a kept row that does rule it out is there.
     *
     * <p>Both rows are kept: the first for the other item, the second for the line. The table says
     * the second settles the line and the first does not, and the input a person is shown for the
     * line is where the row that settles it stands.
     */
    @Test
    void aKeptRowThatSettlesTheLineIsShownBeforeTheOneComposedForItThatDoesNot() {
        ObligationIdentity other = new ObligationIdentity.OfABorder(
                TheLinesBesideABorder.aLineOverTwoPositions().obligation(),
                aDirection(-1));
        SequencedMap<ObligationIdentity, RowKey> composedFor = new LinkedHashMap<>();
        composedFor.put(LINE, COMPOSED_FOR_IT);
        SequencedMap<RowKey, Map<ObligationIdentity, Settlement>> byRow = new LinkedHashMap<>();
        byRow.put(COMPOSED_FOR_IT,
                Map.of(LINE, new Settlement.DoesNotSettle(), other, new Settlement.Settles()));
        byRow.put(COMPOSED_FOR_SOMETHING_ELSE,
                Map.of(LINE, new Settlement.Settles(), other, new Settlement.DoesNotSettle()));
        SequencedMap<RowKey, Map<ObligationIdentity, InputOfARowForALine>> standsAt =
                new LinkedHashMap<>();
        standsAt.put(COMPOSED_FOR_SOMETHING_ELSE, Map.of(LINE, standing(2, 5)));
        Settlements table = new Settlements(List.of(LINE, other), composedFor, byRow, standsAt,
                Map.of(LINE, standing(1, 3)));

        Set<RowKey> kept = table.keeping();
        assertEquals(Set.of(COMPOSED_FOR_IT, COMPOSED_FOR_SOMETHING_ELSE), kept,
                "each row is the only one settling one of the two items, so both are kept");
        assertEquals("x = 2, y = 5", table.shownFor(kept).get(LINE).at().orElseThrow().said(),
                "the line is shown where the row that rules it out stands, and not where the row"
                        + " composed for it and kept for something else does");
    }

    /**
     * The same, where the row that rules the line out stands at no input the line's reading names
     * — as a row at a point in a region does not. It is still the row for the line: which row is
     * handed for a line and whether its input there can be said are two questions, and a row
     * standing nowhere nameable does not hand the line to the row composed for it, which does not
     * rule it out.
     */
    @Test
    void aKeptRowThatSettlesTheLineAtNoNameableInputIsStillTheRowForIt() {
        ObligationIdentity other = new ObligationIdentity.OfABorder(
                TheLinesBesideABorder.aLineOverTwoPositions().obligation(),
                aDirection(-1));
        SequencedMap<ObligationIdentity, RowKey> composedFor = new LinkedHashMap<>();
        composedFor.put(LINE, COMPOSED_FOR_IT);
        SequencedMap<RowKey, Map<ObligationIdentity, Settlement>> byRow = new LinkedHashMap<>();
        byRow.put(COMPOSED_FOR_IT,
                Map.of(LINE, new Settlement.DoesNotSettle(), other, new Settlement.Settles()));
        byRow.put(COMPOSED_FOR_SOMETHING_ELSE,
                Map.of(LINE, new Settlement.Settles(), other, new Settlement.DoesNotSettle()));
        Settlements table = new Settlements(List.of(LINE, other), composedFor, byRow,
                new LinkedHashMap<>(), Map.of(LINE, standing(1, 3)));

        Set<RowKey> kept = table.keeping();
        assertEquals(Set.of(COMPOSED_FOR_IT, COMPOSED_FOR_SOMETHING_ELSE), kept,
                "each row is the only one settling one of the two items, so both are kept");
        Settlements.Shown shown = table.shownFor(kept).get(LINE);
        assertEquals(COMPOSED_FOR_SOMETHING_ELSE, shown.rowKey(),
                "the line is the row's that rules it out, though no input of it can be said");
        assertEquals(Optional.empty(), shown.at(),
                "and no input is named for it, rather than the input of the row that does not");
    }

    /** And a line no kept row is offered for is a line nothing here names a place for. */
    @Test
    void aLineNoKeptRowIsOfferedForIsShownNoPlace() {
        assertNull(bothSettleIt().shownFor(Set.of()).get(LINE),
                "what is shown then is what the measurement saw, which is the finding's own");
    }

    /**
     * A row composed for a line was composed somewhere, and a table saying otherwise is refused.
     *
     * <p>The two are separate maps and a caller fills both, so this is the one place the pair is
     * held together. Left to whoever fills them, a line with a row and no input is a line the
     * report shows the measurement's own answer for while the block hands the row over — which is
     * the state this whole reading exists to keep out.
     */
    @Test
    void aRowComposedForALineAndComposedNowhereIsRefused() {
        SequencedMap<ObligationIdentity, RowKey> composedFor = new LinkedHashMap<>();
        composedFor.put(LINE, COMPOSED_FOR_IT);
        SequencedMap<RowKey, Map<ObligationIdentity, Settlement>> byRow = new LinkedHashMap<>();
        byRow.put(COMPOSED_FOR_IT, Map.of(LINE, new Settlement.Settles()));

        assertThrows(IllegalArgumentException.class,
                () -> new Settlements(List.of(LINE), composedFor, byRow, new LinkedHashMap<>(),
                        Map.of()),
                "a line whose row was composed nowhere is a state nothing downstream reads right");
    }

    /**
     * Two rows that both tell the line's two lines apart, one of them composed for it.
     *
     * <p>Which is the state this is about: the table says both answer it, and the reduction is free
     * to keep either.
     */
    private static Settlements bothSettleIt() {
        SequencedMap<ObligationIdentity, RowKey> composedFor = new LinkedHashMap<>();
        composedFor.put(LINE, COMPOSED_FOR_IT);
        SequencedMap<RowKey, Map<ObligationIdentity, Settlement>> byRow = new LinkedHashMap<>();
        byRow.put(COMPOSED_FOR_SOMETHING_ELSE, Map.of(LINE, new Settlement.Settles()));
        byRow.put(COMPOSED_FOR_IT, Map.of(LINE, new Settlement.Settles()));
        SequencedMap<RowKey, Map<ObligationIdentity, InputOfARowForALine>> standsAt =
                new LinkedHashMap<>();
        standsAt.put(COMPOSED_FOR_SOMETHING_ELSE, Map.of(LINE, standing(2, 5)));
        standsAt.put(COMPOSED_FOR_IT, Map.of(LINE, standing(1, 3)));
        return new Settlements(List.of(LINE), composedFor, byRow, standsAt,
                Map.of(LINE, standing(1, 3)));
    }

    private static InputOfARowForALine standing(int x, int y) {
        Map<NumericTerm, Place> at = new LinkedHashMap<>();
        at.put(new NumericTerm.ValueOf(TermPath.of("x")), Count.of(x));
        at.put(new NumericTerm.ValueOf(TermPath.of("y")), Count.of(y));
        return new InputOfARowForALine(TheLinesBesideABorder.aLineOverTwoPositions(), at);
    }

    /** The fixture's line held against {@code -3 * x + y}, one line of its family. */
    private static ObligationIdentity aLine() {
        return new ObligationIdentity.OfABorder(
                TheLinesBesideABorder.aLineOverTwoPositions().obligation(), aDirection(-3));
    }

    /** {@code weight * x + y}. */
    private static QuantityKey aDirection(int weight) {
        Map<NumericTerm, ExactRatio> direction = new LinkedHashMap<>();
        direction.put(new NumericTerm.ValueOf(TermPath.of("x")), ExactRatio.of(weight));
        direction.put(new NumericTerm.ValueOf(TermPath.of("y")), ExactRatio.ONE);
        return new QuantityKey(direction);
    }
}
