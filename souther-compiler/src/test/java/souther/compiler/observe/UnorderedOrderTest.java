package souther.compiler.observe;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The order the parts of a collection that states none are written in: their places where every one
 * has a place, and their text where any one has none.
 */
class UnorderedOrderTest {

    private static final Map<String, Place> PLACES = Map.of(
            "-11", Count.of(-11), "-3", Count.of(-3), "2", Count.of(2), "10", Count.of(10),
            "2.0", Count.of(2));

    private static List<String> ordered(List<String> parts, Function<String, Place> placeOf) {
        return UnorderedOrder.of(parts, placeOf, Function.identity());
    }

    @Test
    void partsWithPlacesAreInTheOrderOfTheirPlacesAndNotOfTheirText() {
        assertEquals(List.of("-11", "-3", "2", "10"),
                ordered(List.of("10", "2", "-3", "-11"), PLACES::get));
    }

    @Test
    void twoPartsAtOnePlaceAreSeparatedByTheirText() {
        assertEquals(List.of("2", "2.0"), ordered(List.of("2.0", "2"), PLACES::get));
        assertEquals(List.of("2", "2.0"), ordered(List.of("2", "2.0"), PLACES::get));
    }

    /** One part without a place puts every part in the order of its text, so that no two of them
     *  are compared by one rule and a third by another. */
    @Test
    void aPartWithNoPlaceOrdersAllOfThemByText() {
        assertEquals(List.of("-11", "-3", "10", "2", "x"),
                ordered(List.of("10", "2", "x", "-3", "-11"), PLACES::get));
    }

    @Test
    void theOrderDoesNotDependOnTheOrderThePartsAreHandedIn() {
        List<String> parts = new ArrayList<>(List.of("10", "2", "-3", "-11", "2.0"));
        List<String> first = ordered(parts, PLACES::get);
        for (int turn = 0; turn < parts.size(); turn++) {
            Collections.rotate(parts, 1);
            assertEquals(first, ordered(parts, PLACES::get));
        }
        Collections.reverse(parts);
        assertEquals(first, ordered(parts, PLACES::get));
    }

    @Test
    void theListHandedInIsLeftAsItIs() {
        List<String> parts = List.of("10", "2");

        ordered(parts, PLACES::get);

        assertEquals(List.of("10", "2"), parts);
    }

    /** Nothing is asked about a collection that has no order to settle, so a reader that costs
     *  something to answer is never made to. */
    @Test
    void nothingIsAskedAboutFewerThanTwoParts() {
        Function<String, Place> neverAsked = part -> {
            throw new AssertionError("asked where " + part + " sits");
        };

        assertEquals(List.of(), UnorderedOrder.of(List.<String>of(), neverAsked, part -> {
            throw new AssertionError("asked how " + part + " is written");
        }));
        assertEquals(List.of("10"), UnorderedOrder.of(List.of("10"), neverAsked, part -> {
            throw new AssertionError("asked how " + part + " is written");
        }));
    }

    @Test
    void eachPartIsWrittenOnce() {
        List<String> asked = new ArrayList<>();
        UnorderedOrder.of(List.of("10", "2", "-3"), PLACES::get, part -> {
            asked.add(part);
            return part;
        });

        assertEquals(3, asked.size());
    }
}
