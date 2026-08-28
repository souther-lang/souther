package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Towards;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Where a rule parts a quantity's values, as against the number the rule wrote.
 *
 * <p>The two are the same level only by coincidence. A carrier that counts has a next value, so a
 * rule refusing its own threshold keeps the values from one count in; a carrier that does not has
 * none, so such a rule keeps everything up to the threshold and never reaches it. Read as the
 * number written, a range some other reading stopped at the value the rule leaves disagrees with it
 * by exactly one count — and the disagreement is invisible wherever the rule admits its threshold,
 * which is half the operators an author can write.
 *
 * <p>Held here directly, on a seam built from an order and a threshold, so that what a reader of one
 * gets is fixed before any reader is asked what it does with it.
 *
 * <p>The rule's own side is what a reader wants: what it keeps stops there. The other side is the
 * first value it refuses, and the two are one count apart wherever the order steps.
 */
class WhereARulePartsTheValuesIsNotTheNumberItWroteTest {

    /** The whole numbers, which is the order a count is on. */
    private static final LevelSpace STEPS = LevelSpace.onACarrier(Carrier.WHOLE);

    /** An order with no next value, where a refused threshold has nothing one count in. */
    private static final LevelSpace FILLS = LevelSpace.onACarrier(Carrier.DENSE);

    private static Level at(Carrier carrier, long count) {
        return new Level.OnACarrier(carrier, Count.of(count));
    }

    /**
     * One row: an order, the number a rule wrote, which side that number belongs to, and where the
     * values actually part.
     *
     * @param belongsTo the side the threshold's own value falls on, which is what the operator says
     * @param below     the last value on the lower side, or null where the order names none
     * @param above     the first value on the upper side, or null on the same reading
     */
    private record Row(String rule, LevelSpace space, Carrier carrier, long wrote,
                       Towards belongsTo, Long below, Long above) {}

    /**
     * Every way an ordering can stand to the value it names, on an order that steps.
     *
     * <p>{@code x <= 0} keeps zero, so the lower side ends at zero and the upper begins at one.
     * {@code x < 0} refuses it, so the lower side ends at minus one and the upper begins at zero.
     * The two are the same written number and two divisions of the whole numbers.
     */
    private static final List<Row> ON_AN_ORDER_THAT_STEPS = List.of(
            new Row("x <= 0", STEPS, Carrier.WHOLE, 0, Towards.BELOW, 0L, 1L),
            new Row("x < 0", STEPS, Carrier.WHOLE, 0, Towards.ABOVE, -1L, 0L),
            new Row("x >= 0", STEPS, Carrier.WHOLE, 0, Towards.ABOVE, -1L, 0L),
            new Row("x > 0", STEPS, Carrier.WHOLE, 0, Towards.BELOW, 0L, 1L));

    /** The side a rule keeps ends where the values part, and that is not always what it wrote. */
    @Test
    void anOrderThatStepsPartsOneCountInFromARefusedThreshold() {
        for (Row row : ON_AN_ORDER_THAT_STEPS) {
            Seam parts = Seam.of(row.space(), at(row.carrier(), row.wrote()), row.belongsTo());

            assertEquals(at(row.carrier(), row.below()), parts.below(),
                    () -> row.rule() + ": the last value below");
            assertEquals(at(row.carrier(), row.above()), parts.above(),
                    () -> row.rule() + ": the first value above");
        }
    }

    /**
     * And the two operators that name one number are two divisions of it.
     *
     * <p>The whole point, said as a comparison rather than as two rows: {@code x < 0} and
     * {@code x <= 0} write the same number and part the values one count apart. A reader holding the
     * number cannot tell them apart, and a reader holding the seam cannot confuse them.
     */
    @Test
    void twoOperatorsOverOneNumberAreTwoDivisions() {
        Seam admits = Seam.of(STEPS, at(Carrier.WHOLE, 0), Towards.BELOW);
        Seam refuses = Seam.of(STEPS, at(Carrier.WHOLE, 0), Towards.ABOVE);

        assertNotEquals(admits.below(), refuses.below(),
                "one keeps the zero and the other does not, over one written number");
        assertEquals(at(Carrier.WHOLE, 0), admits.below());
        assertEquals(at(Carrier.WHOLE, -1), refuses.below());
    }

    /**
     * An order that does not step names no value on the side a rule refuses its threshold from.
     *
     * <p>Which is the answer, not a gap in one: the values come arbitrarily close to the line and
     * none of them is the last. A reader stepping here would be naming a value the language does not
     * write, and one refusing the line for having no neighbour would drop a division the model
     * states.
     */
    @Test
    void anOrderThatFillsNamesNoValueBesideTheLine() {
        Seam parts = Seam.of(FILLS, at(Carrier.DENSE, 0), Towards.BELOW);

        assertEquals(at(Carrier.DENSE, 0), parts.below(), "the value it keeps is its own");
        assertNull(parts.above(), "and there is no first value above it to name");
    }

    /**
     * What the rule wrote is kept beside where the values part, because a reader needs both.
     *
     * <p>The number is what an author wrote and what a report prints; the seam is where the rows go.
     * Held as one value, a report naming the row's level would print a number the author never
     * wrote, and a search looking at the written number would look where the quantity stands at
     * nothing.
     */
    @Test
    void theNumberTheRuleWroteIsKeptBesideWhereTheValuesPart() {
        Seam parts = Seam.of(STEPS, at(Carrier.WHOLE, 0), Towards.ABOVE);

        assertEquals(at(Carrier.WHOLE, 0), parts.at().written(),
                "the line is still at the number the rule wrote");
        assertEquals(at(Carrier.WHOLE, -1), parts.below(),
                "and the values part one count in from it");
    }
}
