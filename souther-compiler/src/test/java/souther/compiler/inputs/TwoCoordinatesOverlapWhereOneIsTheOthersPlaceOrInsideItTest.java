package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two numbers are apart when no place of one is a place of the other, and not for being two
 * numbers: a number read off a place moves with a number read off the same place by another
 * operation, or off a place inside it.
 */
class TwoCoordinatesOverlapWhereOneIsTheOthersPlaceOrInsideItTest {

    private static final TermPath X = TermPath.of("x");

    private static final TermPath XS = TermPath.of("xs");

    @Test
    void theSamePlaceOverlapsItself() {
        assertTrue(FilingCoordinate.at(X).overlaps(FilingCoordinate.at(X)));
    }

    @Test
    void aPlaceInsideAnotherOverlapsItBothWays() {
        FilingCoordinate container = FilingCoordinate.at(XS);
        FilingCoordinate element = FilingCoordinate.at(XS.element());
        assertTrue(container.overlaps(element));
        assertTrue(element.overlaps(container));
    }

    @Test
    void placesApartDoNotOverlap() {
        assertFalse(FilingCoordinate.at(X).overlaps(FilingCoordinate.at(XS)));
        assertFalse(FilingCoordinate.at(XS.element()).overlaps(FilingCoordinate.at(X)));
    }
}
