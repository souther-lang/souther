package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The numbers at two coordinates may move together where what each is read off bears on what the
 * other is ({@link FilingCoordinate#sharesAPlaceWith}), and not where each is filed: how many times
 * a value occurs in a run is filed under the run and read off the value as well.
 */
class TwoCoordinatesMoveTogetherWhereWhatTheirNumbersAreReadOffBearsTest {

    private static final TermPath RUN = TermPath.of("xs").element().element();
    private static final TermPath KEY = TermPath.of("k");
    private static final TermPath OTHER = TermPath.of("o");

    private static FilingCoordinate occurrencesOf(TermPath key) {
        return FilingCoordinate.of(
                NumericTerm.OccurrencesOfAKey.of(new RunSource.FlattenedOccurrences(RUN), key));
    }

    @Test
    void aCountMovesWithTheValueItCountsThoughTheyAreFiledApart() {
        FilingCoordinate count = occurrencesOf(KEY);
        FilingCoordinate value = FilingCoordinate.of(new NumericTerm.ValueOf(KEY));
        assertFalse(count.path().bearsOn(value.path()));
        assertTrue(count.sharesAPlaceWith(value));
        assertTrue(value.sharesAPlaceWith(count));
    }

    /** A position the reading got no further than is the value there. */
    @Test
    void aPositionNoNumberWasNamedAtIsTheValueThere() {
        assertTrue(occurrencesOf(KEY).sharesAPlaceWith(FilingCoordinate.at(KEY)));
        assertTrue(FilingCoordinate.at(KEY).sharesAPlaceWith(occurrencesOf(KEY)));
        assertTrue(FilingCoordinate.at(KEY).sharesAPlaceWith(FilingCoordinate.at(KEY)));
    }

    @Test
    void numbersReadOffPlacesApartDoNot() {
        assertFalse(occurrencesOf(KEY).sharesAPlaceWith(
                FilingCoordinate.of(new NumericTerm.ValueOf(OTHER))));
        assertFalse(FilingCoordinate.at(OTHER).sharesAPlaceWith(occurrencesOf(KEY)));
    }
}
