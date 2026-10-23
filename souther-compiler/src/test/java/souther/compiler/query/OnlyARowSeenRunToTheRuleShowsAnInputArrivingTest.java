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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

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
                        readBack)), null);
    }

    /** What the rows {@code one} saw run to the rule read back. */
    private static List<ObservedInputs> seen(ARowTellingTheLinesApart.AtOneReading one) {
        return one.seenThere().stream().map(ItemAssessment.Attempt.Certified::readBack).toList();
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

        assertEquals(List.of(readBack), seen(searched(true, readBack)));
    }

    /** A row a search built and saw run to the rule, read back as {@code readBack}. */
    private static ItemAssessment.Attempt.Certified ran(ObservedInputs readBack) {
        return new ItemAssessment.Attempt.Certified(
                new Generator.GeneratedRow(new Generator.Purpose.Unstated(), List.of()),
                WayToTheBorder.UNTOUCHED, CompositionAccount.NOTHING, true, readBack);
    }

    /** One search of one place that built {@code rows}, in that order. */
    private static ARowTellingTheLinesApart.AtOneReading searchedInto(
            List<ItemAssessment.Attempt> rows) {
        Map<NumericTerm, Place> at = new LinkedHashMap<>();
        at.put(X, Count.of(1));
        at.put(Y, Count.of(3));
        return new ARowTellingTheLinesApart.AtOneReading(
                TheLinesBesideABorder.aLineOverTwoPositions(), beside(), at,
                SearchOutcomes.each(rows), null);
    }

    /**
     * A search that built a row for each way of standing in what the behavior depends on, of which
     * the first ran there and settles nothing and the second settles the line: the second is what
     * settles it and what is offered for it, and the first does not stand in its place.
     */
    @Test
    void everyRowSeenRunToTheRuleIsAskedAndTheOneThatSettlesIsOffered() {
        ItemAssessment.Attempt.Certified first = ran(InputsOfTheBody.aRowOfNoInputsReadBack());
        ItemAssessment.Attempt.Certified second = ran(InputsOfTheBody.aRowOfNoInputsReadBack());
        Map<NumericTerm, Place> apart = new LinkedHashMap<>();
        apart.put(X, Count.of(2));
        apart.put(Y, Count.of(7));

        ARowTellingTheLinesApart.AtOneReading settled = searchedInto(List.of(first, second))
                .settledBy(seen -> seen == second ? Optional.of(apart) : Optional.empty());

        assertSame(second, settled.settling().row());
        assertEquals(apart, settled.settling().at());
        assertSame(second, settled.composed().orElseThrow());
    }

    /** The control: where no row settles the line, nothing is settled and the row the searches
     *  offer is offered. */
    @Test
    void whereNoRowSettlesTheLineTheSearchesOfferTheirOwn() {
        ItemAssessment.Attempt.Certified first = ran(InputsOfTheBody.aRowOfNoInputsReadBack());
        ItemAssessment.Attempt.Certified second = ran(InputsOfTheBody.aRowOfNoInputsReadBack());

        ARowTellingTheLinesApart.AtOneReading settled = searchedInto(List.of(first, second))
                .settledBy(_ -> Optional.empty());

        assertNull(settled.settling());
        assertSame(first, settled.composed().orElseThrow());
    }

    /** The control: the same row, read back at the place and not seen reaching the comparison. */
    @Test
    void aRowNotSeenRunToTheRuleShowsNothingArriving() {
        assertEquals(List.of(), seen(searched(false, InputsOfTheBody.aRowOfNoInputsReadBack())));
    }
}
