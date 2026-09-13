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
import static org.junit.jupiter.api.Assertions.assertFalse;
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

    private static final RealizationTarget SETTLED =
            new RealizationTarget.AtOnePosition(new NumericTerm.ValueOf(TermPath.of("a")));
    private static final RealizationTarget ANCHOR =
            new RealizationTarget.AtOnePosition(new NumericTerm.ValueOf(TermPath.of("b")));

    private static Place at(long n) {
        return new Count(BigDecimal.valueOf(n));
    }

    private static ValuesTried rejecting(Place settled, Place anchored) {
        return ValuesTried.NONE.and(Map.of(SETTLED, settled, ANCHOR, anchored));
    }

    @Test
    @DisplayName("a place is not offered again where the rest of them stand where they stood")
    void thePlaceIsApartUnderTheAnchorItWasTriedUnder() {
        ValuesTried tried = rejecting(at(3), at(10));

        assertEquals(List.of(at(3)), tried.apartFor(SETTLED, Map.of(ANCHOR, at(10))).places());
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

        assertEquals(List.of(at(3)), tried.apartFor(SETTLED, Map.of()).places());
    }

    @Test
    @DisplayName("each position is asked for its own place and not for the one beside it")
    void eachPositionIsApartAtWhatItHeld() {
        ValuesTried tried = rejecting(at(3), at(10));

        assertEquals(List.of(at(10)), tried.apartFor(ANCHOR, Map.of(SETTLED, at(3))).places());
        assertTrue(tried.apartFor(ANCHOR, Map.of(SETTLED, at(4))).isEmpty());
    }

    @Test
    @DisplayName("two arrangements that shared an anchor are both apart under it")
    void everyPlaceTriedUnderOneAnchorIsApart() {
        ValuesTried tried = rejecting(at(3), at(10))
                .and(Map.of(SETTLED, at(4), ANCHOR, at(10)));

        assertEquals(List.of(at(3), at(4)),
                tried.apartFor(SETTLED, Map.of(ANCHOR, at(10))).places());
    }

    /**
     * And a place is the place it is on the order, however either of them was written.
     *
     * <p>Which is what a search spends its figure on. A run's own representative is written as the
     * order writes it and a rule's value as an author wrote it, so the two spellings of one place
     * meet exactly where a value is put aside and offered again — and a point would be tried with
     * one value as many times as this compiler allows it values at all.
     */
    @Test
    @DisplayName("a place tried is apart from the same place spelled another way")
    void aPlaceIsApartHoweverEitherOfThemWasWritten() {
        ValuesTried tried = rejecting(new Count(new BigDecimal("3.0")), at(10));

        assertTrue(tried.apartFor(SETTLED, Map.of(ANCHOR, at(10))).has(at(3)),
                "three and three point oh are one place on the order");
        assertTrue(tried.apartFor(SETTLED, Map.of(ANCHOR, new Count(new BigDecimal("10.0"))))
                        .has(at(3)),
                "and so is the place the rest of them are standing at");
    }

    /**
     * And an arrangement written another way is the arrangement, not a second one.
     *
     * <p>What the figure counts is values the point was tried with. Two spellings kept as two, a
     * point would spend the figure twice over on one value and the run beside it would never be
     * reached.
     */
    @Test
    @DisplayName("the same arrangement spelled another way is remembered once")
    void oneArrangementIsRememberedOnce() {
        ValuesTried tried = rejecting(at(3), at(10))
                .and(Map.of(SETTLED, new Count(new BigDecimal("3.0")),
                        ANCHOR, new Count(new BigDecimal("10.00"))));

        assertEquals(1, tried.rejected().size(), "one arrangement was tried, written two ways");
    }

    /**
     * And a whole arrangement is asked for as one, which is what a search that chooses for every
     * target at once has to ask.
     *
     * <p>Beside the projection above and not instead of it. A walk that reaches an assignment
     * before anything is built has all of them in hand, and the one thing it may not offer is the
     * arrangement a row was already built from — every other arrangement standing one of those
     * places is one nothing has tried.
     */
    @Test
    @DisplayName("a whole arrangement is held, and one that differs anywhere is not")
    void aWholeArrangementIsHeldAndOthersAreNot() {
        ValuesTried tried = rejecting(at(3), at(10));

        assertTrue(tried.holds(Map.of(SETTLED, at(3), ANCHOR, at(10))));
        assertFalse(tried.holds(Map.of(SETTLED, at(3), ANCHOR, at(20))),
                "the same place for one of them is not the same arrangement");
        assertFalse(tried.holds(Map.of(SETTLED, at(3))),
                "and an arrangement of fewer of them is not it either");
    }
}
