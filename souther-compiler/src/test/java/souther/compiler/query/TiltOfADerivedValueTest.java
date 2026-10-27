package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.query.TiltOfADerivedValue.RowsOnABorder;
import souther.compiler.query.TiltOfADerivedValue.Rule;
import souther.compiler.query.TiltOfADerivedValue.Standing;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What the evidence of the borders of each call of a computation comes to, per position.
 *
 * <p>A weight is fixed where the computation weighing it one more and the one weighing it one less
 * each fail some row, so each way a claim can be overstated is a case here: a row that the changed
 * computation puts on the side the model has it on, evidence taken from a call it is not evidence
 * of, or from a walk that left rows or readings out.
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

    /** The rule that holds where the weighed sum reaches {@code threshold}. */
    private static Rule reaches(long threshold) {
        return (weights, values) -> {
            ExactRatio sum = ExactRatio.ZERO;
            for (Map.Entry<NumericTerm, ExactRatio> each : weights.entrySet()) {
                ExactRatio part = each.getValue()
                        .times(Count.number(values.get(each.getKey())).exactly()).orNull();
                sum = part == null ? null : sum.plus(part).orNull();
                if (sum == null) {
                    return Optional.empty();
                }
            }
            return Optional.of(sum.compareTo(ExactRatio.of(BigInteger.valueOf(threshold))) >= 0);
        };
    }

    private static List<Map<NumericTerm, Place>> held(Row... readings) {
        return Arrays.stream(readings).map(Row::held).toList();
    }

    /** A border at {@code threshold} with the rows nearest it, where the rule holds and where it
     *  does not; which is which is the rule's to say. */
    private static RowsOnABorder border(long threshold, boolean complete, List<Row> holding,
                                        List<Row> notHolding) {
        List<Row> nearest = new ArrayList<>(holding);
        nearest.addAll(notHolding);
        return new RowsOnABorder(UNIT_WEIGHTS, reaches(threshold),
                held(nearest.toArray(Row[]::new)), complete);
    }

    private static RowsOnABorder nothingOn(boolean complete) {
        return border(100, complete, List.of(), List.of());
    }

    private static final List<Row> AT_100 = List.of(row(100, 0), row(0, 100));
    private static final List<Row> BESIDE_100 = List.of(row(99, 0), row(0, 99));

    private static Class<? extends Standing> of(SequencedMap<NumericTerm, Standing> standings,
                                                NumericTerm place) {
        return standings.get(place).getClass();
    }

    private static SequencedMap<NumericTerm, Standing> oneCall(RowsOnABorder... borders) {
        return TiltOfADerivedValue.standingsOf(PLACES, List.of(List.of(borders)));
    }

    @Test
    void rowsOnBothSidesThatEveryWrongWeightFailsFixEveryWeight() {
        SequencedMap<NumericTerm, Standing> standings =
                oneCall(border(100, true, AT_100, BESIDE_100));
        assertEquals(Standing.Shown.class, of(standings, A));
        assertEquals(Standing.Shown.class, of(standings, B));
    }

    /** The side where the rule holds catches a position weighed less and the other side one weighed
     *  more, so one side alone fixes neither. */
    @Test
    void rowsOnOneSideOnlyFixNothing() {
        SequencedMap<NumericTerm, Standing> standings =
                oneCall(border(100, true, AT_100, List.of()));
        assertEquals(Standing.NotShown.class, of(standings, A));
        assertEquals(Standing.NotShown.class, of(standings, B));
    }

    /**
     * Rows on both sides of both borders, with a position negative where the rule does not hold: the
     * computation weighing {@code a} twice puts every one of them where the model does, so none
     * catches it, and the rows of both borders together are of full rank.
     */
    @Test
    void rowsOnBothSidesThatAWrongWeightPassesDoNotFixThatWeight() {
        RowsOnABorder low = border(100, true, List.of(row(100, 0), row(99, 1)),
                List.of(row(-1, 100), row(-2, 101)));
        RowsOnABorder high = border(1000, true, List.of(row(1000, 0), row(999, 1)),
                List.of(row(-1, 1000), row(-2, 1001)));
        SequencedMap<NumericTerm, Standing> standings = oneCall(low, high);
        assertEquals(Standing.NotShown.class, of(standings, A));
        assertEquals(Standing.Shown.class, of(standings, B));
    }

    /** Two calls on exclusive branches: the rows on the border of one are on none of the other's,
     *  and the weight is fixed for the computation only where it is fixed for both. */
    @Test
    void aWeightIsFixedForAComputationOnlyWhereEveryCallFixesIt() {
        SequencedMap<NumericTerm, Standing> standings = TiltOfADerivedValue.standingsOf(PLACES,
                List.of(List.of(border(100, true, AT_100, BESIDE_100)),
                        List.of(nothingOn(true))));
        assertEquals(Standing.NotShown.class, of(standings, A));
        assertEquals(Standing.NotShown.class, of(standings, B));
    }

    /** One value handed to two calls puts the same rows on both, and each is fixed together. */
    @Test
    void callsPutToTheSameRowsAreFixedTogether() {
        RowsOnABorder same = border(100, true, AT_100, BESIDE_100);
        SequencedMap<NumericTerm, Standing> standings =
                TiltOfADerivedValue.standingsOf(PLACES, List.of(List.of(same), List.of(same)));
        assertEquals(Standing.Shown.class, of(standings, A));
        assertEquals(Standing.Shown.class, of(standings, B));
    }

    /** A call none of whose borders was read is unread, and not a call that fixes nothing. */
    @Test
    void aCallNothingWasReadAgainstLeavesTheWeightUndecidedAndNotUnfixed() {
        SequencedMap<NumericTerm, Standing> standings = TiltOfADerivedValue.standingsOf(PLACES,
                List.of(List.of(border(100, true, AT_100, BESIDE_100)), List.of()));
        assertEquals(Standing.Undecided.class, of(standings, A));
        assertEquals(Standing.Undecided.class, of(standings, B));
    }

    /** Evidence that is not every reading of every row fixes what it fixes and unfixes nothing. */
    @Test
    void aWalkThatWentWithoutReadingsFixesWhatItFixedAndLeavesTheRestUndecided() {
        SequencedMap<NumericTerm, Standing> standings = oneCall(border(100, false,
                List.of(row(100, 0)), List.of(row(99, 0))));
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
        SequencedMap<NumericTerm, Standing> standings = oneCall(
                border(100, true, List.of(row(100, 0)), List.of(row(99, 0))), nothingOn(false));
        assertEquals(Standing.Shown.class, of(standings, A));
        assertEquals(Standing.Undecided.class, of(standings, B));
    }

    /** A sum the exact arithmetic cannot hold is a row nobody can say anything of: what the others
     *  catch stays caught, and what they leave is no longer known to be uncaught. */
    @Test
    void aRowTheArithmeticGivesOutOnLeavesWhatTheOthersCatchCaught() {
        Rule overflowsAtB = (weights, values) -> Count.number(values.get(B)).exactly().isZero()
                ? reaches(100).holdsAt(weights, values) : Optional.empty();
        RowsOnABorder border = new RowsOnABorder(UNIT_WEIGHTS, overflowsAtB,
                held(row(100, 0), row(0, 100), row(99, 0), row(0, 99)), true);
        SequencedMap<NumericTerm, Standing> standings = oneCall(border);
        assertEquals(Standing.Shown.class, of(standings, A));
        assertEquals(Standing.Undecided.class, of(standings, B));
    }

    /** Evidence from borders of one call weighing the positions in different scales: each border
     *  puts a changed computation to its own rule, and the weights are those of its own weighing. */
    @Test
    void bordersOfOneCallInDifferentWeighingsAreEachPutToTheirOwnRule() {
        ExactRatio two = ExactRatio.of(BigInteger.TWO);
        Map<NumericTerm, ExactRatio> twice = Map.of(A, two, B, two);
        RowsOnABorder first = new RowsOnABorder(twice, reaches(200),
                held(row(100, 0), row(99, 0)), true);
        RowsOnABorder second = border(100, true, List.of(row(0, 100)), List.of(row(0, 99)));
        SequencedMap<NumericTerm, Standing> standings = oneCall(first, second);
        assertEquals(Standing.Shown.class, of(standings, A));
        assertEquals(Standing.Shown.class, of(standings, B));
    }

    @Test
    void theOrderOfTheCallsAndBordersDecidesNothing() {
        RowsOnABorder one = border(100, true, List.of(row(100, 0)), List.of(row(99, 0)));
        RowsOnABorder other = border(100, true, List.of(row(0, 100)), List.of(row(0, 99)));
        SequencedMap<NumericTerm, Standing> forward = oneCall(one, other);
        SequencedMap<NumericTerm, Standing> backward = oneCall(other, one);
        assertInstanceOf(Standing.Shown.class, forward.get(A));
        assertEquals(of(forward, A), of(backward, A));
        assertEquals(of(forward, B), of(backward, B));
    }
}
