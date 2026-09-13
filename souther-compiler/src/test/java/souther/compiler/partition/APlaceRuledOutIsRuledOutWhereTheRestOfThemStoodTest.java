package souther.compiler.partition;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a search rules out is the positions standing together and not a value of one of them.
 *
 * <p>A row is built from every position at once, so a row that did not stand says that arrangement
 * did not stand. Remembered as the value alone, the same value would be refused under an
 * arrangement of the others nothing has tried yet — and the search would give up a point it still
 * had a row for, on the strength of a row it built somewhere else.
 */
class APlaceRuledOutIsRuledOutWhereTheRestOfThemStoodTest {

    private static final NumericTerm.FromOnePosition SETTLED =
            new NumericTerm.ValueOf(TermPath.of("a"));
    private static final NumericTerm.FromOnePosition ANCHOR =
            new NumericTerm.ValueOf(TermPath.of("b"));

    private static Place at(long n) {
        return new Count(BigDecimal.valueOf(n));
    }

    private static ValuesTried rejecting(Place settled, Place anchored) {
        return ValuesTried.NONE.and(Map.of(
                new RealizationTarget.AtOnePosition(SETTLED), settled,
                new RealizationTarget.AtOnePosition(ANCHOR), anchored));
    }

    @Test
    @DisplayName("a place is not offered again where the rest of them stand where they stood")
    void thePlaceIsApartUnderTheAnchorItWasTriedUnder() {
        ValuesTried tried = rejecting(at(3), at(10));

        assertEquals(List.of(at(3)), tried.apartFor(SETTLED, Map.of(ANCHOR, at(10))));
    }

    @Test
    @DisplayName("and is offered where one of them stands somewhere else")
    void thePlaceIsOfferedUnderAnotherAnchor() {
        ValuesTried tried = rejecting(at(3), at(10));

        assertTrue(tried.apartFor(SETTLED, Map.of(ANCHOR, at(20))).isEmpty());
    }

    @Test
    @DisplayName("a caller that has not reached the rest of them is told what was tried at all")
    void nothingGivenLeavesEveryArrangementStanding() {
        ValuesTried tried = rejecting(at(3), at(10));

        assertEquals(List.of(at(3)), tried.apartFor(SETTLED, Map.of()));
    }

    @Test
    @DisplayName("each position is asked for its own place and not for the one beside it")
    void eachPositionIsApartAtWhatItHeld() {
        ValuesTried tried = rejecting(at(3), at(10));

        assertEquals(List.of(at(10)), tried.apartFor(ANCHOR, Map.of(SETTLED, at(3))));
        assertTrue(tried.apartFor(ANCHOR, Map.of(SETTLED, at(4))).isEmpty());
    }

    @Test
    @DisplayName("two arrangements that shared an anchor are both apart under it")
    void everyPlaceTriedUnderOneAnchorIsApart() {
        ValuesTried tried = rejecting(at(3), at(10)).and(Map.of(
                new RealizationTarget.AtOnePosition(SETTLED), at(4),
                new RealizationTarget.AtOnePosition(ANCHOR), at(10)));

        assertEquals(List.of(at(3), at(4)), tried.apartFor(SETTLED, Map.of(ANCHOR, at(10))));
    }
}
