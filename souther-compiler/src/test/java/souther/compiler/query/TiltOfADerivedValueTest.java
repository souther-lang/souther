package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.query.TiltOfADerivedValue.Evidence;
import souther.compiler.query.TiltOfADerivedValue.Standing;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What the evidence of the borders of each call of a computation comes to, per position.
 *
 * <p>The decision is a function of the evidence and nothing else, so each way a claim can be
 * overstated is a case here: evidence taken from a call it is not evidence of, from a reading
 * away from the border, or from a walk that left rows or readings out.
 */
class TiltOfADerivedValueTest {

    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("a"));
    private static final NumericTerm B = new NumericTerm.ValueOf(TermPath.of("b"));
    private static final List<NumericTerm> PLACES = List.of(A, B);
    private static final Map<NumericTerm, ExactRatio> UNIT_WEIGHTS =
            Map.of(A, ExactRatio.ONE, B, ExactRatio.ONE);

    /** What the two positions hold at a reading of a row. */
    private record Row(long a, long b) {

        Map<NumericTerm, Place> held() {
            Map<NumericTerm, Place> out = new LinkedHashMap<>();
            out.put(A, Count.of(a));
            out.put(B, Count.of(b));
            return out;
        }
    }

    private static Row row(long a, long b) {
        return new Row(a, b);
    }

    private static Evidence on(boolean complete, Row... readings) {
        return onWeighed(UNIT_WEIGHTS, complete, readings);
    }

    private static Evidence onWeighed(Map<NumericTerm, ExactRatio> weights, boolean complete,
                                      Row... readings) {
        return new Evidence(weights, Arrays.stream(readings).map(Row::held).toList(), complete);
    }

    private static Evidence nothingOn(boolean complete) {
        return new Evidence(UNIT_WEIGHTS, List.of(), complete);
    }

    private static Class<? extends Standing> of(SequencedMap<NumericTerm, Standing> standings,
                                                NumericTerm place) {
        return standings.get(place).getClass();
    }

    private static SequencedMap<NumericTerm, Standing> oneCall(Evidence... borders) {
        return TiltOfADerivedValue.standingsOf(PLACES, List.of(List.of(borders)));
    }

    @Test
    void rowsThatSpanThePositionsFixEveryWeightOfTheCall() {
        SequencedMap<NumericTerm, Standing> standings =
                oneCall(on(true, row(100, 0), row(0, 100)));
        assertEquals(Standing.Shown.class, of(standings, A));
        assertEquals(Standing.Shown.class, of(standings, B));
    }

    /** Evidence is the readings that stand at the border, and a row with a reading away from it is
     *  one the caller asked about by its standing reading alone. */
    @Test
    void oneIndependentVectorFixesOnlyWhatItReaches() {
        SequencedMap<NumericTerm, Standing> standings = oneCall(on(true, row(100, 0)));
        assertEquals(Standing.Shown.class, of(standings, A));
        assertEquals(Standing.NotShown.class, of(standings, B));
    }

    /** Two calls on exclusive branches: the rows on the border of one are on none of the other's,
     *  and the weight is fixed for the computation only where it is fixed for both. */
    @Test
    void aWeightIsFixedForAComputationOnlyWhereEveryCallFixesIt() {
        SequencedMap<NumericTerm, Standing> standings = TiltOfADerivedValue.standingsOf(PLACES,
                List.of(List.of(on(true, row(100, 0), row(0, 100))), List.of(nothingOn(true))));
        assertEquals(Standing.NotShown.class, of(standings, A));
        assertEquals(Standing.NotShown.class, of(standings, B));
    }

    /** One value handed to two calls puts the same rows on both, and each is fixed together. */
    @Test
    void callsPutToTheSameRowsAreFixedTogether() {
        Evidence same = on(true, row(100, 0), row(0, 100));
        SequencedMap<NumericTerm, Standing> standings =
                TiltOfADerivedValue.standingsOf(PLACES, List.of(List.of(same), List.of(same)));
        assertEquals(Standing.Shown.class, of(standings, A));
        assertEquals(Standing.Shown.class, of(standings, B));
    }

    /** A call none of whose borders was read is unread, and not a call that fixes nothing. */
    @Test
    void aCallNothingWasReadAgainstLeavesTheWeightUndecidedAndNotUnfixed() {
        SequencedMap<NumericTerm, Standing> standings = TiltOfADerivedValue.standingsOf(PLACES,
                List.of(List.of(on(true, row(100, 0), row(0, 100))), List.of()));
        assertEquals(Standing.Undecided.class, of(standings, A));
        assertEquals(Standing.Undecided.class, of(standings, B));
    }

    /** Evidence that is not every reading of every row fixes what it fixes and unfixes nothing. */
    @Test
    void aWalkThatWentWithoutReadingsFixesWhatItFixedAndLeavesTheRestUndecided() {
        SequencedMap<NumericTerm, Standing> standings = oneCall(on(false, row(100, 0)));
        assertEquals(Standing.Shown.class, of(standings, A));
        assertEquals(Standing.Undecided.class, of(standings, B));
    }

    /** A border no row is on is read to say so only where the rows were read. */
    @Test
    void aBorderNoRowIsOnUnfixesTheWeightsOnlyWhereTheRowsWereRead() {
        assertEquals(Standing.NotShown.class, of(oneCall(nothingOn(true)), A));
        assertEquals(Standing.Undecided.class, of(oneCall(nothingOn(false)), A));
    }

    /** One border unread among the borders of a call: the rest cannot say the weight is unfixed. */
    @Test
    void aBorderOfTheCallThatWasNotReadLeavesTheWeightsUndecided() {
        SequencedMap<NumericTerm, Standing> standings =
                oneCall(on(true, row(100, 0)), nothingOn(false));
        assertEquals(Standing.Shown.class, of(standings, A));
        assertEquals(Standing.Undecided.class, of(standings, B));
    }

    /** Evidence from borders of one call weighing the positions in different scales is one space:
     *  the model's weights multiply each row, and the fixed weight is a property of the position. */
    @Test
    void bordersOfOneCallInDifferentWeighingsPutTheirRowsTogether() {
        ExactRatio half = ExactRatio.of(BigInteger.ONE, BigInteger.TWO);
        Map<NumericTerm, ExactRatio> halves = Map.of(A, half, B, half);
        Evidence first = onWeighed(halves, true, row(200, 0));
        Evidence second = on(true, row(0, 100));
        SequencedMap<NumericTerm, Standing> standings = oneCall(first, second);
        assertEquals(Standing.Shown.class, of(standings, A));
        assertEquals(Standing.Shown.class, of(standings, B));
    }

    @Test
    void theOrderOfTheCallsAndBordersDecidesNothing() {
        Evidence one = on(true, row(100, 0));
        Evidence other = on(true, row(0, 100));
        SequencedMap<NumericTerm, Standing> forward = oneCall(one, other);
        SequencedMap<NumericTerm, Standing> backward = oneCall(other, one);
        assertInstanceOf(Standing.Shown.class, forward.get(A));
        assertEquals(of(forward, A), of(backward, A));
        assertEquals(of(forward, B), of(backward, B));
    }
}
