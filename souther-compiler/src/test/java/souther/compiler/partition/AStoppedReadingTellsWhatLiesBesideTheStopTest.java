package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.StatedComparison;
import souther.compiler.inputs.WhatARelationLeavesUndivided;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
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

    private static final String OVER_RATIONALS = """
            module g

            data Yes
            data No

            behavior classify : (n: Decimal, m: Decimal, k: Int) -> Yes | No
            let classify (n, m, k) = if %s then Yes else No
            """;

    private static final String CHECKED = """
            module g

            data Yes
            data No
            data Pos = Int
                invariant positive = value > 0

            behavior classify : (n: Int, m: Int, k: Int) -> Yes | No
            let classify (n, m, k) = if %s then Yes else No
            """;

    private static ReadComparisons readOf(String condition) {
        return readOf(SOURCE, condition);
    }

    private static ReadComparisons readOf(String source, String condition) {
        return ReadComparisons.of(source.formatted(condition), "classify");
    }

    private static StatedComparison statedOf(ReadComparisons read) {
        return ((ComparisonReadings.Stated.AComparison) read.only().statement()).comparison();
    }

    /** What the lines drawn from the comparison of {@code condition} are told it works out. */
    private static UndividedByARelation.Working workingOfTheStop(String condition) {
        return workingOfTheStop(SOURCE, condition);
    }

    private static UndividedByARelation.Working workingOfTheStop(String source,
                                                                 String condition) {
        ReadComparisons read = readOf(source, condition);
        ComparisonReadings.Reading against = read.only();
        AffineReading.OfAComparison arithmetic = AffineReading.read(statedOf(read),
                against.reads(), read.inputs().reading(read.rules()));
        assertTrue(arithmetic instanceof AffineReading.OfAComparison.Stopped,
                () -> condition + " is read to a stop");
        return AffineReading.OfAComparison.workingOf(arithmetic);
    }

    /** What the rule that reads the comparison of {@code condition} tells of its rows. */
    private static UndividedByARelation.Working workingOfTheRule(String condition) {
        return workingOfTheRule(SOURCE, condition);
    }

    private static UndividedByARelation.Working workingOfTheRule(String source,
                                                                 String condition) {
        ReadComparisons read = readOf(source, condition);
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
     * What is worked out on the number a quotient comes to is not the quotient's: the quotient
     * answers wherever its divisor is not nought, and the sum with one that follows is a sum of its
     * own, which the lines drawn on the dividend and the divisor do not keep their rows from.
     */
    @Test
    void anOperationOnTheNumberAQuotientComesToIsNotTheQuotientsToAnswerFor() {
        assertNotEquals(WhatARelationLeavesUndivided.Told.EVERY,
                workingOfTheRule("n / m + 1 >= 100").told());
        assertNotEquals(WhatARelationLeavesUndivided.Told.EVERY,
                workingOfTheRule(OVER_RATIONALS, "n / m + n >= m").told());
    }

    /**
     * Two expressions the reading cannot read are two stops, and only the first is held for its
     * owner to answer for: where the divisor of the second is nought a run stops, and nothing here
     * tells of it.
     */
    @Test
    void aSecondStopIsNotTheFirstOnesToAnswerFor() {
        UndividedByARelation.Working working = workingOfTheStop("m * k + n / m >= 100");
        assertNotEquals(WhatARelationLeavesUndivided.Told.EVERY, working.told());
        assertNotEquals(UndividedByARelation.Working.NOTHING, working);
    }

    /**
     * A construction checks the invariant of the type it makes, which stops a run, whatever the
     * stop under it is.
     */
    @Test
    void aConstructionAroundTheStopStillChecksItsInvariant() {
        assertEquals(UndividedByARelation.Working.UNREAD,
                workingOfTheStop(CHECKED, "Pos(m * k).value + n >= 100"));
    }

    /**
     * A quotient added to a product is no quotient of the kind the quotient's analysis reads, so
     * its lines are not told to work out nothing beyond their operands. The product is a stop of
     * its own beside the quotient, and no row is shown computed for either.
     */
    @Test
    void aQuotientAddedToAProductIsNotTheQuotientsToAnswerFor() {
        assertEquals(UndividedByARelation.Working.UNREAD,
                workingOfTheRule("n / m + k * k >= 100"));
    }
}
