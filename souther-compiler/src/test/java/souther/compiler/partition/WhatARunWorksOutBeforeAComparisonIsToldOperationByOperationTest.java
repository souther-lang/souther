package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a run works out before a comparison is told as the operations it is, each where it stops a
 * run: a newtype's construction at the run its clauses leave, each application of a closure over
 * a list written out over what that application is handed, a total of such a list at the ends of
 * an {@code Int}, and a number rounded to a whole one where the way of rounding puts the ends.
 *
 * <p>The comparison relates the fixed part of the first month to a number of the input. Where
 * nothing before it can stop a run, every row reaches it, and the line it draws on the other
 * number is where the fixed part ends. Where something before it stops the runs with some amounts,
 * the rows that reach it hold the others, and the line moves to where those end — so the line says
 * where each operation was held to stop, and not only that it was told. One that is not told ties
 * the places it reads, and the comparison is not shown to be reached at every value of them.
 */
class WhatARunWorksOutBeforeAComparisonIsToldOperationByOperationTest {

    private static final String MODEL = """
            module probe

            data Yen = Int
                invariant value >= 0

            data Hole = Int
                invariant value == 0 || value == 100

            data Pay = { base: Yen, extra: Yen, variable: Yen }
                invariant base.value <= 1000000000000
                invariant extra.value <= 1000000000000
                invariant variable.value <= 1000000000000

            data Month = { days: Int, pay: Pay }
            data Window = { first: Month, second: Month, third: Month }

            data Unchanged = { n: Int }
            data Changed = { n: Int, y: Yen, h: Hole }

            let fixedOf (p: Pay): Yen = p.base + p.extra
            let totalOf (p: Pay): Yen = fixedOf(p) + p.variable
            let monthsOf (w: Window): List<Month> = [ w.first, w.second, w.third ]
            let averageOf (months: List<Month>): Yen =
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(m -> totalOf(m.pay).value, months)) / List.length(months)))

            behavior judge : (previous: Yen, window: Window) -> Unchanged | Changed
                constructs Yen, Hole, Unchanged, Changed

            let judge (previous, window) = {
                let before = %s
                if fixedOf(window.first.pay) == previous then Unchanged { n = %s }
                else Changed { n = %s, y = Yen(0), h = Hole(0) }
            }
            """;

    /** The classes of {@code previous} where the fixed part of the first month runs to its end. */
    private static final List<String> NOTHING_STOPS_BEFORE_IT =
            List.of("previous/0 <= x < 2000000000001", "previous/2000000000001 <= x");

    /** The same where the base of the first month is nought on every run that gets past. */
    private static final List<String> THE_BASE_IS_NOUGHT =
            List.of("previous/0 <= x < 1000000000001", "previous/1000000000001 <= x");

    /**
     * The model with {@code before} worked out ahead of the comparison and read in both arms as
     * {@code read}, so that every run works it out.
     */
    private static PartitionEvidence judged(String before, String read) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(before, read, read),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        PartitionEvidence judge = compilation.db()
                .ask(new Adequacy.Coverage("probe")).value().get("judge");
        assertNotNull(judge, "the model under test is measured");
        return judge;
    }

    private static List<String> previous(PartitionEvidence evidence) {
        return evidence.axes().stream().filter(axis -> axis.path().equals("previous"))
                .findFirst().orElseThrow().classes();
    }

    private static List<String> notReachedAtEveryValue(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .filter(each -> each.reason()
                        == UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    /** The comparison on its own, which every row reaches. */
    @Test
    void nothingWorkedOutBeforeTheComparisonLeavesItsLineAtTheEndOfTheFixedPart() {
        PartitionEvidence evidence = judged("0", "before");

        assertEquals(NOTHING_STOPS_BEFORE_IT, previous(evidence));
        assertEquals(List.of(), notReachedAtEveryValue(evidence),
                () -> evidence.notRead().toString());
    }

    /** {@code base + 1} lies in the run a {@code Yen} holds for every base the declarations
     *  leave, so making one stops no run. */
    @Test
    void aConstructionEveryAmountGetsPastStopsNoRun() {
        PartitionEvidence evidence = judged("Yen(window.first.pay.base.value + 1)",
                "before.value");

        assertEquals(NOTHING_STOPS_BEFORE_IT, previous(evidence));
        assertEquals(List.of(), notReachedAtEveryValue(evidence),
                () -> evidence.notRead().toString());
    }

    /** {@code 0 - base} is a {@code Yen} only where the base is nought. */
    @Test
    void aConstructionStopsTheRunsWhoseNumberIsOutsideTheRunItsClausesLeave() {
        PartitionEvidence evidence = judged("Yen(0 - window.first.pay.base.value)",
                "before.value");

        assertEquals(THE_BASE_IS_NOUGHT, previous(evidence));
        assertEquals(List.of(), notReachedAtEveryValue(evidence),
                () -> evidence.notRead().toString());
    }

    /**
     * The clauses of a type with a hole in it leave no one run, so where its making stops a run is
     * not told, and the places it reads are left tied: what a run gets past there is not said.
     */
    @Test
    void aConstructionWhoseClausesLeaveAHoleIsNotTold() {
        PartitionEvidence evidence = judged("Hole(window.first.pay.base.value)", "before.value");

        assertEquals(List.of("window.first.pay.base", "window.first.pay.extra"),
                notReachedAtEveryValue(evidence), () -> evidence.notRead().toString());
    }

    /**
     * One closure applied to two months is two operations, each over the month it is handed: the
     * second application, over the first month, is what holds its base to nought. Applied to the
     * second month alone, nothing holds the first.
     */
    @Test
    void eachApplicationOfAClosureIsToldOverWhatItIsHanded() {
        PartitionEvidence both = judged(
                "List.map(m -> Yen(0 - m.pay.base.value), [ window.second, window.first ])",
                "List.length(before)");
        assertEquals(THE_BASE_IS_NOUGHT, previous(both));
        assertEquals(List.of(), notReachedAtEveryValue(both), () -> both.notRead().toString());

        PartitionEvidence second = judged(
                "List.map(m -> Yen(0 - m.pay.base.value), [ window.second ])",
                "List.length(before)");
        assertEquals(NOTHING_STOPS_BEFORE_IT, previous(second));
    }

    /**
     * Where one application is handed a value no form is read of — a number that turns on which
     * arm a run takes — the construction in the body is told on none of them: the first
     * application's telling says nothing of the second's, and the places the closure is handed are
     * left tied.
     */
    @Test
    void aBodyToldOnSomeApplicationsOnlyIsLeftUnsaid() {
        PartitionEvidence evidence = judged("List.map(n -> Yen(0 - n),"
                        + " [ window.second.pay.base.value,"
                        + " if window.second.days > 0 then window.first.pay.base.value else 0 ])",
                "List.length(before)");

        assertEquals(List.of("window.first.pay.base", "window.first.pay.extra"),
                notReachedAtEveryValue(evidence), () -> evidence.notRead().toString());
    }

    /**
     * A closure applied to the elements a filter keeps is applied on some runs only, and what its
     * body works out is not told: the places it reads are left tied.
     */
    @Test
    void aClosureAppliedToWhatAFilterKeepsIsNotTold() {
        PartitionEvidence evidence = judged("List.map(m -> Yen(0 - m.pay.base.value),"
                        + " List.filter(m -> m.days >= 17, [ window.first ]))",
                "List.length(before)");

        assertEquals(List.of("window.first.pay.base", "window.first.pay.extra"),
                notReachedAtEveryValue(evidence), () -> evidence.notRead().toString());
    }

    /**
     * A number rounded and made a {@code Yen} stops a run where it rounds below nought, which is
     * where the way of rounding puts it: toward nought, {@code -base / 3} is nought for a base up
     * to two; toward minus infinity, only for nought.
     */
    @Test
    void aRoundingMadeAValueIsHeldWhereTheWayOfRoundingPutsTheEnds() {
        PartitionEvidence down = judged(
                "Yen(Rational.toInt(DOWN, (0 - window.first.pay.base.value) / 3))",
                "before.value");
        assertEquals(List.of("previous/0 <= x < 1000000000003", "previous/1000000000003 <= x"),
                previous(down));

        PartitionEvidence floor = judged(
                "Yen(Rational.toInt(FLOOR, (0 - window.first.pay.base.value) / 3))",
                "before.value");
        assertEquals(THE_BASE_IS_NOUGHT, previous(floor));
    }


    /**
     * A total of a list written out is held to an {@code Int} once it is added up: four million
     * times the base three times over is one only up to a base of 768614336404, though each of the
     * three is one for every base the declarations leave.
     */
    @Test
    void aTotalIsHeldToAnIntOnceItIsAddedUp() {
        PartitionEvidence evidence = judged("[ List.sum(List.map(m -> m.pay.base.value * 4000000,"
                        + " [ window.first, window.first, window.first ])) ]",
                "List.length(before)");

        assertEquals(List.of("previous/0 <= x < 1768614336405", "previous/1768614336405 <= x"),
                previous(evidence));
    }

    /**
     * The average of three months, each amount bounded at the place it stands: every operation it
     * works out — the sums of each month, made a {@code Yen}, the total, the quotient, the rounding
     * and the {@code Yen} it is made — is got past by every row, and the comparison is reached as
     * though nothing were worked out before it.
     */
    @Test
    void theAverageOfBoundedAmountsLeavesTheComparisonReachedAtEveryValue() {
        PartitionEvidence evidence = judged("averageOf(monthsOf(window))", "before.value");

        assertEquals(NOTHING_STOPS_BEFORE_IT, previous(evidence));
        assertEquals(List.of(), notReachedAtEveryValue(evidence),
                () -> evidence.notRead().toString());
    }
}
