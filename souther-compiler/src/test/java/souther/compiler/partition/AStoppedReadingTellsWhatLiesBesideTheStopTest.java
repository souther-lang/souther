package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.StatedComparison;
import souther.compiler.inputs.WhatARelationLeavesUndivided;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison the reading stopped at tells what the program works out beside the expression it
 * stopped at. The expression is its analysis's to answer for; an operation beside it is worked out
 * on every row and is told, so that a row where it stops is not taken as computed.
 */
class AStoppedReadingTellsWhatLiesBesideTheStopTest {

    private static final String SOURCE = """
            module g

            data Yes
            data No

            behavior classify : (n: Int, m: Int, k: Int) -> Yes | No
            let classify (n, m, k) = if %s then Yes else No
            """;

    private static ReadComparisons readOf(String condition) {
        return ReadComparisons.of(SOURCE.formatted(condition), "classify");
    }

    private static StatedComparison statedOf(ReadComparisons read) {
        return ((ComparisonReadings.Stated.AComparison) read.only().statement()).comparison();
    }

    /** What the lines drawn from the comparison of {@code condition} are told it works out. */
    private static UndividedByARelation.Working workingOfTheStop(String condition) {
        ReadComparisons read = readOf(condition);
        ComparisonReadings.Reading against = read.only();
        AffineReading.OfAComparison arithmetic = AffineReading.read(statedOf(read),
                against.reads(), read.inputs().reading(read.rules()));
        assertTrue(arithmetic instanceof AffineReading.OfAComparison.Stopped,
                () -> condition + " is read to a stop");
        return AffineReading.OfAComparison.workingOf(arithmetic);
    }

    /** What the rule that reads the comparison of {@code condition} tells of its rows. */
    private static UndividedByARelation.Working workingOfTheRule(String condition) {
        ReadComparisons read = readOf(condition);
        ComparisonReadings.Reading against = read.only();
        return Pullback.ofAComparisonOnTheInput(statedOf(read), against.reads(),
                read.inputs().reading(read.rules())).working().get();
    }

    @Test
    void nothingBesideTheProductLeavesTheSizesOfTheFormToAnswer() {
        assertEquals(UndividedByARelation.Working.NOTHING, workingOfTheStop("m * k >= 100"));
    }

    /**
     * {@code n + 1} is worked out on every row, and a row at the greatest {@code Int} stops there
     * whatever the product comes to: it is told, though the sum cancels in the form.
     */
    @Test
    void anOperationBesideTheProductIsTold() {
        UndividedByARelation.Working working = workingOfTheStop("(n + 1) - 1 + m * k >= 100");
        assertEquals(WhatARelationLeavesUndivided.Told.EVERY, working.told());
        assertTrue(working.operations().stream().anyMatch(each ->
                        each.form().coefs().size() == 1 && each.form().constant().signum() > 0),
                working::toString);
    }

    /**
     * The quotient of two positions works out neither a product with the number nor anything else:
     * every row where the divisor is not nought is computed, so no size of a place is held back.
     */
    @Test
    void aQuotientByAnInputIsToldToWorkOutNothingBeyondItsOperands() {
        UndividedByARelation.Working working = workingOfTheRule("n / m >= 100");
        assertEquals(WhatARelationLeavesUndivided.Told.EVERY, working.told());
        assertTrue(working.operations().isEmpty(), working::toString);
    }

    @Test
    void theOperandsOfAQuotientAreWorkedOutOnEveryRowOfIt() {
        UndividedByARelation.Working working = workingOfTheRule("(n + 1) / m >= 100");
        assertEquals(WhatARelationLeavesUndivided.Told.EVERY, working.told());
        assertEquals(1, working.operations().size(), working::toString);
    }

    /**
     * A quotient added to a product is no quotient of the kind the quotient's analysis reads, so
     * its lines are not told to work out nothing beyond their operands: they keep the answer of
     * a stop.
     */
    @Test
    void aQuotientAddedToAProductIsNotTheQuotientsToAnswerFor() {
        assertEquals(UndividedByARelation.Working.NOTHING,
                workingOfTheRule("n / m + k * k >= 100"));
    }
}
