package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.partition.ObligationIdentity;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The input a report names for a line is where the row a person is handed stands, and not where the
 * row composed for it stood.
 *
 * <p>A row that tells two lines apart answers the line whoever it was composed for, which is what
 * the table of settlements says. So the reduction may drop the row composed for the line — another
 * row already offers for it, and a row whose going costs the offering nothing goes
 * ({@link Settlements#keeping}). The place shown has to follow that, or a reader is shown one input
 * and handed a row at another.
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
                        .get(LINE).said(),
                "the row composed for the line is the one a person is handed for it");
    }

    @Test
    void andTheRowThatIsLeftNamesItOnceTheReductionHasDroppedThatOne() {
        Settlements table = bothSettleIt();

        assertEquals("x = 2, y = 5",
                table.shownFor(Set.of(COMPOSED_FOR_SOMETHING_ELSE)).get(LINE).said(),
                "a row composed for something else answers the line as much, so when the row"
                        + " composed for it goes the input shown is where that one stands");
    }

    /** And a line no row that is left answers is a line nothing here names a place for. */
    @Test
    void aLineNoKeptRowAnswersIsShownNoPlace() {
        assertNull(bothSettleIt().shownFor(Set.of()).get(LINE),
                "what is shown then is what the measurement saw, which is the finding's own");
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
        SequencedMap<RowKey, Map<ObligationIdentity, WhereARowStandsOnALine>> standsAt =
                new LinkedHashMap<>();
        standsAt.put(COMPOSED_FOR_SOMETHING_ELSE, Map.of(LINE, standing(2, 5)));
        standsAt.put(COMPOSED_FOR_IT, Map.of(LINE, standing(1, 3)));
        return new Settlements(List.of(LINE), composedFor, byRow, standsAt);
    }

    private static WhereARowStandsOnALine standing(int x, int y) {
        Map<NumericTerm, Place> at = new LinkedHashMap<>();
        at.put(new NumericTerm.ValueOf(TermPath.of("x")), Count.of(x));
        at.put(new NumericTerm.ValueOf(TermPath.of("y")), Count.of(y));
        return new WhereARowStandsOnALine(TheLinesBesideABorder.aLineOverTwoPositions(), at);
    }

    private static ObligationIdentity aLine() {
        return new ObligationIdentity.OfABorder(
                TheLinesBesideABorder.aLineOverTwoPositions().obligation());
    }
}
