package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.DecimalOperation.Formed;
import souther.compiler.inputs.DecimalOperation.Written;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Term;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What is shown of a run of a decimal term is shown of the numbers the room for a decimal operation
 * is assured for, and by the operations and not by the rows that were built.
 *
 * <p>Whether a decimal operation has room turns on the scale its operands are written at and not on
 * how large they are: a product asks for the sum of its factors' scales, so {@code 0} and
 * {@code 168} are worked out against a factor at the floor of the range and {@code 0.5} between
 * them is not. A row built at each end of a run says nothing of the values between, which for a
 * whole number it does.
 */
class ADenseTermIsShownOnlyOfTheNumbersTheRoomIsAssuredForTest {

    private static final NumericDomain.Bounds HOURS = new NumericDomain.Bounds(
            Endpoint.inclusive(Count.of(0)), Endpoint.inclusive(Count.of(168)));

    private static Term<String> hours(String place, long weight) {
        return new Term<>(List.of(place), ExactRatio.of(weight), HOURS, HOURS, null, true,
                Granularity.DENSE, NumericDomain.Bounds.OPEN, place);
    }

    /** {@code 4h - s >= 0}, the hours from nought to 168 on both sides. */
    private static final List<Term<String>> TERMS = List.of(hours("h", 4), hours("s", -1));

    private static Leaves hoursLeft(DecimalOperation operation) {
        return WhatARelationLeavesUndivided.leavesOf(TERMS, 0, ExactRatio.ZERO, Rel.GE,
                String::equals, (one, other) -> true, Granularity.DENSE, null, List.of(),
                new Operations(List.of(), List.of(operation), Told.EVERY));
    }

    /** {@code h * factor}, with {@code h} a place of the input. */
    private static DecimalOperation hoursTimes(BigDecimal factor) {
        return new DecimalOperation(BinOp.MUL,
                List.of(new Formed(Map.of("h", ExactRatio.ONE), ExactRatio.ZERO),
                        new Written(factor)),
                List.of());
    }

    private static DecimalOperation sum(DecimalOperation.Operand one, DecimalOperation.Operand two) {
        return new DecimalOperation(BinOp.ADD, List.of(one, two), List.of());
    }

    private static DecimalOperation product(DecimalOperation.Operand one,
                                            DecimalOperation.Operand two) {
        return new DecimalOperation(BinOp.MUL, List.of(one, two), List.of());
    }

    private static final Formed A_PLACE = new Formed(Map.of("h", ExactRatio.ONE), ExactRatio.ZERO);

    @Test
    void theRoomIsShownForOperationsOverNumbersAtAFewPlaces() {
        assertTrue(DecimalOperation.haveRoomWhateverTheNumbers(List.of()));
        assertTrue(DecimalOperation.haveRoomWhateverTheNumbers(List.of(
                sum(A_PLACE, new Written(new BigDecimal("5.0"))),
                product(new DecimalOperation.Worked(0), new Written(new BigDecimal("4.0"))))));
    }

    @Test
    void theRoomIsNotShownForAFactorAtTheFloorOfTheRangeOrForProductsThatGrowPastIt() {
        assertFalse(DecimalOperation.haveRoomWhateverTheNumbers(List.of(
                sum(A_PLACE, new Written(new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE))))));
        List<DecimalOperation> chain = new ArrayList<>();
        chain.add(product(A_PLACE, A_PLACE));
        for (int i = 1; i < 200; i++) {
            chain.add(product(new DecimalOperation.Worked(i - 1), A_PLACE));
        }
        assertFalse(DecimalOperation.haveRoomWhateverTheNumbers(chain));
    }

    @Test
    void anOperationReadingOneNotWorkedOutBeforeItHasNoRoomShown() {
        assertFalse(DecimalOperation.haveRoomWhateverTheNumbers(List.of(
                product(new DecimalOperation.Worked(0), new Written(BigDecimal.ONE)))));
    }

    @Test
    void aFactorAtAScaleTheRoomIsAssuredForShowsTheTermOverTheWholeRun() {
        assertInstanceOf(Leaves.Settled.class, hoursLeft(hoursTimes(new BigDecimal("4.0"))));
    }

    @Test
    void aFactorAtTheFloorOfTheRangeShowsNothingThoughBothEndsAreWorkedOut() {
        BigDecimal atTheFloor = new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE);
        assertNull(hoursLeft(hoursTimes(atTheFloor)));
    }
}
