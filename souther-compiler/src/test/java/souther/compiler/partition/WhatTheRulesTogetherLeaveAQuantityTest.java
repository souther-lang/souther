package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The runs of values several rules leave one quantity.
 *
 * <p>Several rules can cut one quantity and they are one arrangement however they were written:
 * {@code n > 10} and {@code n > 20} leave three runs, not two overlapping pairs. What each rule did
 * on its own is a {@link Seam}; what they come to together is here, and it is the one thing both the
 * classes of a position and the points of a border are read off.
 *
 * <p>Built from seams rather than from thresholds, so two spellings of one division contribute one
 * place to part the values rather than two — and the run between them, which no row could ever be
 * written in, never exists to be counted.
 */
class WhatTheRulesTogetherLeaveAQuantityTest {

    private static final Carrier WHOLE = new Carrier.Whole();
    private static final LevelSpace NUMBERS = LevelSpace.onACarrier(WHOLE);

    private static Level at(String number) {
        return new Level.OnACarrier(WHOLE, new Count(new java.math.BigDecimal(number)));
    }

    /** Where {@code n <= t} parts the whole numbers. */
    private static Seam upTo(String t) {
        return Seam.of(NUMBERS, at(t), Towards.BELOW);
    }

    /** Where {@code n < t} parts them, which is the same place as {@code n <= t - 1}. */
    private static Seam under(String t) {
        return Seam.of(NUMBERS, at(t), Towards.ABOVE);
    }

    /** How the runs read, as the two seams each of them lies between. */
    private static List<String> bandsOf(Seam... parted) {
        return QuantityArrangement.of(NUMBERS, List.of(parted)).bands().stream()
                .map(Band::key).toList();
    }

    /**
     * One cut leaves two runs, and both of them run to the order's own end.
     *
     * <p>The ends are the order's and are not seams. A run with nothing parting it at one end is
     * where the quantity itself stops, and writing a seam there would owe a row against a line no
     * rule drew.
     */
    @Test
    void oneCutLeavesTwoRuns() {
        assertEquals(List.of("|4", "5|"), bandsOf(upTo("4")));
    }

    /** Two cuts leave three, and the middle one runs between them. */
    @Test
    void twoCutsLeaveThreeRuns() {
        assertEquals(List.of("|10", "11|20", "21|"),
                bandsOf(upTo("10"), upTo("20")));
    }

    /** Three leave four, in the order the values are in and not the order the rules were written. */
    @Test
    void threeCutsLeaveFourRunsInTheOrderOfTheValues() {
        assertEquals(List.of("|10", "11|20", "21|30", "31|"),
                bandsOf(upTo("30"), upTo("10"), upTo("20")));
    }

    /**
     * Two rules that part the values in one place leave one seam and no run between them.
     *
     * <p>The defect this is built to make impossible. {@code n <= 4} and {@code n < 5} are one
     * division of the whole numbers; taken as two thresholds they leave a run above four and below
     * five, and a report counts a class that no row can ever be written in.
     */
    @Test
    void twoSpellingsOfOneDivisionLeaveNoRunBetweenThem() {
        assertEquals(List.of("|4", "5|"),
                bandsOf(upTo("4"), under("5")));
    }
}
