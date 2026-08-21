package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Towards;

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
        return within(null, null, parted);
    }

    /** The same, where the rules leave the quantity only what lies between two values. */
    private static List<String> within(String low, String high, Seam... parted) {
        return QuantityArrangement.of(NUMBERS, List.of(parted),
                        low == null ? null : at(low), high == null ? null : at(high))
                .bands().stream().map(Band::key).toList();
    }

    /**
     * A run says which values are in it, and the ends it names are in it.
     *
     * <p>Both ends inclusive, because a run is named by the values at its ends rather than by the
     * lines beside it: the first value above a seam is in the run above, and the last value below is
     * in the run below. A reader that took the seam's own numbers for the ends would put the value
     * against the line on the wrong side of it.
     */
    @Test
    void aRunHoldsTheValuesFromItsFirstToItsLast() {
        Band mid = QuantityArrangement.of(NUMBERS, List.of(upTo("10"), upTo("20"))).bands().get(1);

        assertEquals(false, mid.holds(at("10")), "ten is the last value below it");
        assertEquals(true, mid.holds(at("11")), "eleven is its first");
        assertEquals(true, mid.holds(at("20")), "twenty is its last");
        assertEquals(false, mid.holds(at("21")), "twenty-one is the first value above it");
    }

    /** And a run with no seam under it runs from wherever the rules start the quantity. */
    @Test
    void aRunWithNothingPartingItBelowRunsFromTheStart() {
        Band first = QuantityArrangement.of(NUMBERS, List.of(upTo("10")), at("0"), null)
                .bands().get(0);

        assertEquals(false, first.holds(at("-1")), "the rules leave nothing below zero");
        assertEquals(true, first.holds(at("0")));
        assertEquals(true, first.holds(at("10")));
        assertEquals(false, first.holds(at("11")));
    }

    /**
     * A run open at a line the quantity names no value beside is read at the line, in its own units.
     *
     * <p>{@code 3 * d <= 1} parts the decimals at a third, which no finite decimal is — so neither
     * run has a value against the line and both are read at the position itself. A third is what the
     * rule wrote over how much of the quantity it wrote it in, and a reader comparing a value of
     * {@code d} against the one the rule carried would put every decimal up to one below the line.
     */
    @Test
    void aRunOpenAtItsLineIsReadInTheQuantitysOwnUnits() {
        java.math.BigDecimal three = new java.math.BigDecimal("3");
        souther.compiler.check.Carrier dense = new souther.compiler.check.Carrier.Dense();
        LevelSpace decimals = LevelSpace.onACarrier(dense);
        Seam third = Seam.of(
                LevelSpace.overFiniteDecimals(LevelSpace.generatorOverFiniteDecimals(three)),
                new Level.ACount(new Count(java.math.BigDecimal.ONE)), Towards.BELOW,
                new Seam.Scale(three, dense));
        Band below = QuantityArrangement.of(decimals, List.of(third)).bands().get(0);

        assertEquals(true, below.holds(decimal(dense, "0.2")), "a fifth is under a third");
        assertEquals(false, below.holds(decimal(dense, "0.5")),
                "and a half is over it, however the rule wrote the line");
    }

    private static Level decimal(souther.compiler.check.Carrier of, String number) {
        return new Level.OnACarrier(of, new Count(new java.math.BigDecimal(number)));
    }

    /**
     * Two rules that part the values at one place, one keeping it and one giving it away.
     *
     * <p>Over a carrier whose values fill, {@code <= 0.5} and {@code < 0.5} are two divisions at one
     * number, and together they leave three runs: everything under it, the number itself, and
     * everything over it. Ordered by a value either of them names — both name 0.5 — the two come out
     * in whichever order they were read, and one of the two orders leaves the middle run open at
     * both ends. Read on, that run holds nothing and disappears, and the two runs either side both
     * hold 0.5.
     */
    @Test
    void twoRulesAtOnePlaceLeaveTheValueItselfBetweenThem() {
        souther.compiler.check.Carrier of = new souther.compiler.check.Carrier.Dense();
        LevelSpace decimals = LevelSpace.onACarrier(of);
        Level half = new Level.OnACarrier(of, new Count(new java.math.BigDecimal("0.5")));
        Seam keeps = Seam.of(decimals, half, Towards.BELOW);
        Seam givesAway = Seam.of(decimals, half, Towards.ABOVE);

        for (List<Seam> order : List.of(List.of(keeps, givesAway), List.of(givesAway, keeps))) {
            assertEquals(List.of("|", "0.5|0.5", "|"),
                    QuantityArrangement.of(decimals, order).bands().stream()
                            .map(Band::key).toList(),
                    "read in either order, the number itself is a run of its own: " + order);
        }
    }

    /**
     * The outermost runs stop where the rules stop the quantity.
     *
     * <p>A bound is not a cut: nothing outside it can be constructed, so there is no run on the far
     * side to cover (ADR-0090). What it does is end the run beside it — the two either side of a
     * line at ten run from the bound and not from the order's own extent.
     */
    @Test
    void theOutermostRunsStopWhereTheRulesStopTheQuantity() {
        assertEquals(List.of("0|10", "11|20", "21|100"), within("0", "100", upTo("10"), upTo("20")));
    }

    /**
     * A place the rules leave nothing at parts nothing.
     *
     * <p>A cut outside what the quantity is left is not a division of it — the values it would tell
     * apart are values no row can be written at — so it is dropped rather than kept as a run holding
     * nothing.
     */
    @Test
    void aCutOutsideWhatTheRulesLeaveDividesNothing() {
        assertEquals(List.of("0|10", "11|100"), within("0", "100", upTo("10"), upTo("200")));
    }

    /**
     * And a run the rules leave no value in is not a run.
     *
     * <p>{@code invariant value <= 10} beside a line at ten leaves everything from eleven up with no
     * value in it. Counted, it is a class an author is told to write a row for and cannot. Judged on
     * the numbers alone it looks inhabited, because eleven is less than the order's own end; what
     * settles it is what the quantity is left, which is nothing above ten.
     */
    @Test
    void aRunTheRulesLeaveNoValueInIsNotARun() {
        assertEquals(List.of("0|10"), within("0", "10", upTo("10")));
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
