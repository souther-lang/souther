package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;
import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ObservedInputs;
import souther.compiler.partition.QuantityKey;
import souther.compiler.partition.WayToTheBorder;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a search for a row ruling a line beside a border out shows arriving is a row it composed
 * and saw run to the rule, as that run read it back — and nothing a search composed that was not
 * seen getting there.
 *
 * <p>A row read back standing in the run beside the line and not seen reaching the comparison is a
 * value at a place, which says nothing of whether a row there arrives; so it shows no input
 * arriving, and the line it was composed for is left where nothing showed one.
 */
class OnlyARowSeenRunToTheRuleShowsAnInputArrivingTest {

    private static final NumericTerm.ValueOf X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final NumericTerm.ValueOf Y = new NumericTerm.ValueOf(TermPath.of("y"));

    private static ARowTellingTheLinesApart.AtOneReading searched(boolean ranThere,
                                                                ObservedInputs readBack) {
        Map<NumericTerm, Place> at = new LinkedHashMap<>();
        at.put(X, Count.of(1));
        at.put(Y, Count.of(3));
        return new ARowTellingTheLinesApart.AtOneReading(
                TheLinesBesideABorder.aLineOverTwoPositions(), beside(), at,
                SearchOutcomes.of(new ItemAssessment.Attempt.Certified(
                        new Generator.GeneratedRow(new Generator.Purpose.Unstated(), List.of()),
                        WayToTheBorder.UNTOUCHED, CompositionAccount.NOTHING, ranThere,
                        readBack)));
    }

    private static AnotherLineTheRowsAllow.Stands beside() {
        Map<NumericTerm, ExactRatio> direction = new LinkedHashMap<>();
        direction.put(X, ExactRatio.of(-3));
        direction.put(Y, ExactRatio.ONE);
        return new AnotherLineTheRowsAllow.Stands(new QuantityKey(direction), ExactRatio.ZERO,
                null, Towards.BELOW, null);
    }

    @Test
    void aRowSeenRunToTheRuleIsTheRowItsRunReadBack() {
        ObservedInputs readBack = InputsOfTheBody.aRowOfNoInputsReadBack();

        assertEquals(Optional.of(readBack), searched(true, readBack).seenThere());
    }

    /** The control: the same row, read back at the place and not seen reaching the comparison. */
    @Test
    void aRowNotSeenRunToTheRuleShowsNothingArriving() {
        assertEquals(Optional.empty(),
                searched(false, InputsOfTheBody.aRowOfNoInputsReadBack()).seenThere());
    }
}
