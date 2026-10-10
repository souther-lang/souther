package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.LinearQuantity;
import souther.compiler.partition.StandingAtAPoint;
import souther.compiler.partition.WayToTheBorder;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which input is named for a line the rows leave standing is one question, and whether the line
 * stands is another.
 *
 * <p>The rows and the model say which line stands. An input the two lines part company at is
 * worked out by stepping along a line, which knows the arithmetic and nothing of what a position's
 * type refuses, so what the declarations are shown to leave nothing at decides only which input is
 * named — and where every input found is one of those, none is, and the line still stands.
 */
class AnInputIsNamedForALineBesideOnlyWhereTheDeclarationsAreNotShownToRefuseItTest {

    private static final int[][] ROWS = {{0, 0}, {0, 1}, {13, 23}, {12, 24}};

    @Test
    void anInputTheDeclarationsRefuseIsPassedOverForAnother() {
        AnotherLineTheRowsAllow.OneDoes plain = named(_ -> false);
        Map<NumericTerm, Place> nearest = plain.tellsApartAt();
        assertNotNull(nearest, "with nothing refused an input is named");

        AnotherLineTheRowsAllow.OneDoes passedOver = named(nearest::equals);

        assertEquals(plain.label(), passedOver.label(), "the line that stands is the same line");
        assertNotNull(passedOver.tellsApartAt(), "and another input is named for it");
        assertNotEquals(nearest, passedOver.tellsApartAt(), "which is not the one refused");
    }

    @Test
    void whereEveryInputIsRefusedTheLineStandsAndNoInputIsNamed() {
        AnotherLineTheRowsAllow.OneDoes plain = named(_ -> false);

        AnotherLineTheRowsAllow.OneDoes refused = named(_ -> true);

        assertEquals(plain.label(), refused.label());
        assertNull(refused.tellsApartAt(),
                "the declarations are shown to leave nothing at any input, so none is named");
        assertTrue(plain.isTheLineOf(refused));
    }

    @Test
    void twoReadingsOfOneLineAgreeWhateverInputEachNames() {
        AnotherLineTheRowsAllow.OneDoes names = named(_ -> false);
        AnotherLineTheRowsAllow.OneDoes namesNone = named(_ -> true);

        assertSame(names, Coverages.besides(names, namesNone));
        assertSame(names, Coverages.besides(namesNone, names));
        assertSame(namesNone, Coverages.besides(namesNone, named(_ -> true)));
    }

    private static AnotherLineTheRowsAllow.OneDoes named(Predicate<Map<NumericTerm, Place>> refused) {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();
        AnotherLineTheRowsAllow said = AnotherLineTheRowsAllow.of(border, true,
                () -> new StandingAtAPoint.RowsRead(rowsOf(border, ROWS), Set.of(),
                        StandingAtAPoint.ReadingsTried.EVERY_ONE, false),
                List.of(), WayToTheBorder.UNTOUCHED, refused);
        return assertInstanceOf(AnotherLineTheRowsAllow.OneDoes.class, said,
                () -> "these rows leave a line standing: " + said);
    }

    /** One reading per row, each value on the term the quantity reads it at. */
    private static List<Map<NumericTerm, Place>> rowsOf(Border border, int[][] rows) {
        List<NumericTerm> terms = new ArrayList<>(
                ((LinearQuantity) border.cut().of()).direction().coefs().keySet());
        terms.sort(Comparator.comparing(NumericTerm::toString));
        List<Map<NumericTerm, Place>> out = new ArrayList<>();
        for (int[] row : rows) {
            Map<NumericTerm, Place> at = new LinkedHashMap<>();
            for (int i = 0; i < terms.size(); i++) {
                at.put(terms.get(i), Count.of(row[i]));
            }
            out.add(at);
        }
        return out;
    }
}
