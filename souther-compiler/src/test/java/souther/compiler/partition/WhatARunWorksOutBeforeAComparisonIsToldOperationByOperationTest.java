package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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
 *
 * <p>Each case is a behavior of one model, measured once for the class at the level that reads the
 * lines and what is left of them: no row has to be built and run for what is asked here.
 */
class WhatARunWorksOutBeforeAComparisonIsToldOperationByOperationTest {

    private static final String DECLARATIONS = """
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
            let noMonths (w: Window): List<Month> = []
            let averageOf (months: List<Month>): Yen =
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(m -> totalOf(m.pay).value, months)) / List.length(months)))
            """;

    /**
     * A behavior working {@code before} out ahead of the comparison and reading it in both arms as
     * {@code read}, so that every run works it out.
     */
    private static final String JUDGED = """

            behavior %1$s : (previous: Yen, window: Window) -> Unchanged | Changed
                constructs Yen, Hole, Unchanged, Changed

            let %1$s (previous, window) = {
                let before = %2$s
                if fixedOf(window.first.pay) == previous then Unchanged { n = %3$s }
                else Changed { n = %3$s, y = Yen(0), h = Hole(0) }
            }
            """;

    private static final String VALUE = "before.value";

    private static final String COUNT = "List.length(before)";

    /** What each case works out before the comparison, and how it reads it after, by name. */
    private static final Map<String, List<String>> CASES = cases();

    private static Map<String, List<String>> cases() {
        Map<String, List<String>> out = new LinkedHashMap<>();
        out.put("nothing", List.of("0", "before"));
        out.put("passed", List.of("Yen(window.first.pay.base.value + 1)", VALUE));
        out.put("refused", List.of("Yen(0 - window.first.pay.base.value)", VALUE));
        out.put("holed", List.of("Hole(window.first.pay.base.value)", VALUE));
        out.put("both", List.of(
                "List.map(m -> Yen(0 - m.pay.base.value), [ window.second, window.first ])",
                COUNT));
        out.put("second", List.of("List.map(m -> Yen(0 - m.pay.base.value), [ window.second ])",
                COUNT));
        out.put("someOnly", List.of("List.map(n -> Yen(0 - n), [ window.second.pay.base.value,"
                + " if window.second.days > 0 then window.first.pay.base.value else 0 ])", COUNT));
        out.put("summedSomeOnly", List.of("[ List.sum(List.map(n -> Yen(0 - n).value,"
                + " [ window.second.pay.base.value,"
                + " if window.second.days > 0 then window.first.pay.base.value else 0 ])) ]",
                COUNT));
        out.put("summedBoth", List.of("[ List.sum(List.map(n -> Yen(0 - n).value,"
                + " [ window.second.pay.base.value, window.first.pay.base.value ])) ]", COUNT));
        out.put("summedInASum", List.of("[ List.sum(List.map(n -> n * 3000000000,"
                + " [ window.second.pay.base.value, window.first.pay.base.value ])) * 0 ]",
                COUNT));
        out.put("summedSomeOnlyInASum", List.of("[ List.sum(List.map(n -> n * 3000000000,"
                + " [ window.second.pay.base.value,"
                + " if window.second.days > 0 then window.first.pay.base.value else 0 ])) * 0 ]",
                COUNT));
        out.put("pastOnEveryRun", List.of(
                "[ 0 * window.first.pay.base.value + 9223372036854775807 + 1 ]", COUNT));
        out.put("summedKept", List.of("[ List.sum(List.map(m -> Yen(0 - m.pay.base.value).value,"
                + " List.filter(m -> m.days >= 17, [ window.first ]))) ]", COUNT));
        out.put("neverApplied", List.of("List.map(m -> Yen(m.days - window.first.pay.base.value),"
                + " noMonths(window))", COUNT));
        out.put("kept", List.of("List.map(m -> Yen(0 - m.pay.base.value),"
                + " List.filter(m -> m.days >= 17, [ window.first ]))", COUNT));
        out.put("down", List.of(
                "Yen(Rational.toInt(DOWN, (0 - window.first.pay.base.value) / 3))", VALUE));
        out.put("floor", List.of(
                "Yen(Rational.toInt(FLOOR, (0 - window.first.pay.base.value) / 3))", VALUE));
        out.put("total", List.of("[ List.sum(List.map(m -> m.pay.base.value * 4000000,"
                + " [ window.first, window.first, window.first ])) ]", COUNT));
        out.put("average", List.of("averageOf(monthsOf(window))", VALUE));
        return out;
    }

    /** Every case measured, by name: one model, compiled and measured once for the class. */
    private static final Map<String, PartitionEvidence> MEASURED = measured();

    private static Map<String, PartitionEvidence> measured() {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        CASES.forEach((name, written) -> source.append(
                JUDGED.formatted(name, written.get(0), written.get(1))));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return compilation.db().ask(new Adequacy.Coverage("probe")).value();
    }

    /** The classes of {@code previous} where the fixed part of the first month runs to its end. */
    private static final List<String> NOTHING_STOPS_BEFORE_IT =
            List.of("previous: 0 <= x < 2000000000001", "previous: 2000000000001 <= x");

    /** The same where the base of the first month is nought on every run that gets past. */
    private static final List<String> THE_BASE_IS_NOUGHT =
            List.of("previous: 0 <= x < 1000000000001", "previous: 1000000000001 <= x");

    private static PartitionEvidence judged(String name) {
        PartitionEvidence evidence = MEASURED.get(name);
        assertNotNull(evidence, () -> name + " is measured");
        return evidence;
    }

    private static List<String> previous(String name) {
        return judged(name).axes().stream().filter(axis -> axis.path().equals("previous"))
                .findFirst().orElseThrow().classes();
    }

    private static List<String> notReachedAtEveryValue(String name) {
        return judged(name).notRead().stream()
                .filter(each -> each.reason()
                        == UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    /** The comparison on its own, which every row reaches. */
    @Test
    void nothingWorkedOutBeforeTheComparisonLeavesItsLineAtTheEndOfTheFixedPart() {
        assertEquals(NOTHING_STOPS_BEFORE_IT, previous("nothing"));
        assertEquals(List.of(), notReachedAtEveryValue("nothing"));
    }

    /** {@code base + 1} lies in the run a {@code Yen} holds for every base the declarations
     *  leave, so making one stops no run. */
    @Test
    void aConstructionEveryAmountGetsPastStopsNoRun() {
        assertEquals(NOTHING_STOPS_BEFORE_IT, previous("passed"));
        assertEquals(List.of(), notReachedAtEveryValue("passed"));
    }

    /** {@code 0 - base} is a {@code Yen} only where the base is nought. */
    @Test
    void aConstructionStopsTheRunsWhoseNumberIsOutsideTheRunItsClausesLeave() {
        assertEquals(THE_BASE_IS_NOUGHT, previous("refused"));
        assertEquals(List.of(), notReachedAtEveryValue("refused"));
    }

    /**
     * The clauses of a type with a hole in it leave no one run, so where its making stops a run is
     * not told, and the places it reads are left tied: what a run gets past there is not said.
     */
    @Test
    void aConstructionWhoseClausesLeaveAHoleIsNotTold() {
        assertEquals(List.of("window.first.pay.base", "window.first.pay.extra"),
                notReachedAtEveryValue("holed"));
    }

    /**
     * One closure applied to two months is two operations, each over the month it is handed: the
     * second application, over the first month, is what holds its base to nought. Applied to the
     * second month alone, nothing holds the first.
     */
    @Test
    void eachApplicationOfAClosureIsToldOverWhatItIsHanded() {
        assertEquals(THE_BASE_IS_NOUGHT, previous("both"));
        assertEquals(List.of(), notReachedAtEveryValue("both"));
        assertEquals(NOTHING_STOPS_BEFORE_IT, previous("second"));
    }

    /**
     * Where one application is handed a value no form is read of — a number that turns on which
     * arm a run takes — the construction in the body is told on none of them: the first
     * application's telling says nothing of the second's, and the places the closure is handed are
     * left tied.
     */
    @Test
    void aBodyToldOnSomeApplicationsOnlyIsLeftUnsaid() {
        assertEquals(List.of("window.first.pay.base", "window.first.pay.extra"),
                notReachedAtEveryValue("someOnly"));
    }

    /**
     * The same applications added up: reading what the total comes to reads each application's
     * number, and where one of them is no form, the reading of the total tells nothing of the
     * body either. What each application works out is told by the walk of what a run works out,
     * on each application, and by nothing that reads a value along the way.
     */
    @Test
    void aBodyAddedUpOnSomeApplicationsOnlyIsLeftUnsaid() {
        assertEquals(List.of("window.first.pay.base", "window.first.pay.extra"),
                notReachedAtEveryValue("summedSomeOnly"));
    }

    /**
     * Added up over what a filter keeps, the construction in the body is made on the runs that keep
     * the month only, so it holds the base to nought on those and on no other: the total's reading
     * reads the body on the month kept, and what it reads there is no operation every run makes.
     */
    @Test
    void aBodyAddedUpOverWhatAFilterKeepsIsLeftUnsaid() {
        assertEquals(List.of("window.first.pay.base", "window.first.pay.extra"),
                notReachedAtEveryValue("summedKept"));
    }

    /**
     * A total read inside a sum is read for the number it comes to, and reading it reads each
     * application's product: that reading is not the run's working out of them. The second
     * application's product, over the first month, is what holds its base to the most three
     * thousand million times of which an {@code Int} holds, whoever reads the total first.
     */
    @Test
    void aTotalReadInsideASumLeavesEachApplicationToBeTold() {
        assertEquals(List.of("previous: 0 <= x < 1003074457346", "previous: 1003074457346 <= x"),
                previous("summedInASum"));
    }

    /**
     * The same where the second application is handed a number no form is read of: the product
     * in the body is told on no application, whatever a reading of the total read of the first,
     * and the places the closure is handed are left tied.
     */
    @Test
    void aTotalReadInsideASumTellsNothingOfABodyReadOnSomeApplicationsOnly() {
        assertEquals(List.of("window.first.pay.base", "window.first.pay.extra"),
                notReachedAtEveryValue("summedSomeOnlyInASum"));
    }

    /** Added up over two months each read, the second application holds the first month's base to
     *  nought as it does where the applications are not added up. */
    @Test
    void aBodyAddedUpOnEveryApplicationIsToldOnEach() {
        assertEquals(THE_BASE_IS_NOUGHT, previous("summedBoth"));
        assertEquals(List.of(), notReachedAtEveryValue("summedBoth"));
    }

    /**
     * A sum that comes to the same number on every run answers on every run or on none: the
     * greatest {@code Int} and one is past it whatever the base is, so every run stops there and
     * no row arrives at the comparison.
     */
    @Test
    void anOperatorPastItsEndsOnEveryRunStopsEveryRun() {
        assertEquals(List.of("previous", "window.first.pay.base", "window.first.pay.extra"),
                judged("pastOnEveryRun").notRead().stream()
                        .filter(each -> each.reason()
                                == UndividedPosition.Reason.NOTHING_ARRIVES_AT_THE_RULES_LINE)
                        .map(PartitionEvidence.NotRead::at).sorted().distinct().toList());
    }

    /**
     * A closure handed a container that holds nothing on any row is applied on no run, so nothing
     * its body works out stops one, however it reads the places outside it.
     */
    @Test
    void aClosureAppliedOnNoRunStopsNone() {
        assertEquals(NOTHING_STOPS_BEFORE_IT, previous("neverApplied"));
        assertEquals(List.of(), notReachedAtEveryValue("neverApplied"));
    }

    /**
     * A closure applied to the elements a filter keeps is applied on some runs only, and what its
     * body works out is not told: the places it reads are left tied.
     */
    @Test
    void aClosureAppliedToWhatAFilterKeepsIsNotTold() {
        assertEquals(List.of("window.first.pay.base", "window.first.pay.extra"),
                notReachedAtEveryValue("kept"));
    }

    /**
     * A number rounded and made a {@code Yen} stops a run where it rounds below nought, which is
     * where the way of rounding puts it: toward nought, {@code -base / 3} is nought for a base up
     * to two; toward minus infinity, only for nought.
     */
    @Test
    void aRoundingMadeAValueIsHeldWhereTheWayOfRoundingPutsTheEnds() {
        assertEquals(List.of("previous: 0 <= x < 1000000000003", "previous: 1000000000003 <= x"),
                previous("down"));
        assertEquals(THE_BASE_IS_NOUGHT, previous("floor"));
    }

    /**
     * A total of a list written out is held to an {@code Int} once it is added up: four million
     * times the base three times over is one only up to a base of 768614336404, though each of the
     * three is one for every base the declarations leave.
     */
    @Test
    void aTotalIsHeldToAnIntOnceItIsAddedUp() {
        assertEquals(List.of("previous: 0 <= x < 1768614336405", "previous: 1768614336405 <= x"),
                previous("total"));
    }

    /**
     * The average of three months, each amount bounded at the place it stands: every operation it
     * works out — the sums of each month, made a {@code Yen}, the total, the quotient, the rounding
     * and the {@code Yen} it is made — is got past by every row, and the comparison is reached as
     * though nothing were worked out before it.
     */
    @Test
    void theAverageOfBoundedAmountsLeavesTheComparisonReachedAtEveryValue() {
        assertEquals(NOTHING_STOPS_BEFORE_IT, previous("average"));
        assertEquals(List.of(), notReachedAtEveryValue("average"));
    }
}
