package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.GaveUp;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule about what an operation answers is worth having only where a construction discharges
 * because of it. So every row of every table is held here to a program that does, and the set is the
 * tables' own rather than a list written beside them: a rule added with no program that fires it
 * fails this, and so does a program left behind by a rule that was removed.
 *
 * <p>A row and not an operation. An operation whose rule is more than one statement — a remainder is
 * bounded at both ends, a rounded value is within one of what it rounds either way — has a program
 * for each, since one program needs one of them and would leave the other free to be dropped.
 *
 * <p>Held to what the library declares as well. Each of these compiles, so a row naming an argument
 * the declaration does not have, or reading a value of a kind the rule is not about, is a failure
 * here and not a silence at whichever call arrives first.
 */
class ARuleAboutAnOperationsResultCarriesSomethingTest {

    private record Discharges(String operation, String module) {}

    private static final List<Discharges> BOUNDED = List.of(
            new Discharges("Int.abs", """
                    module demo
                    data NonNeg = Int
                        invariant value >= 0
                    behavior far : (x: Int) -> NonNeg constructs NonNeg
                    let far (x) = NonNeg(Int.abs(x))
                    """),
            new Discharges("Decimal.abs", """
                    module demo
                    data NonNegD = Decimal
                        invariant value >= 0.0m
                    behavior far : (d: Decimal) -> NonNegD constructs NonNegD
                    let far (d) = NonNegD(Decimal.abs(d))
                    """),
            new Discharges("Int.floorMod", """
                    module demo
                    data Pct = Int
                        invariant value >= 0 && value <= 100
                    behavior wrap : (x: Int) -> Pct constructs Pct
                    let wrap (x) = Pct(Int.floorMod(x, 100))
                    """),
            new Discharges("Decimal.toInt", """
                    module demo
                    data Bad
                    data AtLeastTen = Int
                        invariant value >= 10
                    behavior whole : (d: Decimal) -> AtLeastTen | Bad constructs AtLeastTen
                    let whole (d) = {
                        guard d >= 11.0m
                            else Bad
                        AtLeastTen(Decimal.toInt(HALF_UP, d))
                    }
                    """),
            // The other end of the same operation. One program needs one of the two rows, so a row
            // with no program of its own could be dropped and nothing here would say so.
            new Discharges("Decimal.toInt", """
                    module demo
                    data Bad
                    data BelowTen = Int
                        invariant value < 10
                    behavior whole : (d: Decimal) -> BelowTen | Bad constructs BelowTen
                    let whole (d) = {
                        guard d <= 9.0m
                            else Bad
                        BelowTen(Decimal.toInt(HALF_UP, d))
                    }
                    """),
            new Discharges("Int.floorMod", """
                    module demo
                    data NonNeg = Int
                        invariant value >= 0
                    behavior wrap : (x: Int) -> NonNeg constructs NonNeg
                    let wrap (x) = NonNeg(Int.floorMod(x, 100))
                    """),

            // The measures, whose row is the one every operation that counts what it was given is
            // declared with rather than one written for it. A program each all the same: what the
            // derivation produces is a row like any other, and a row nothing fires is a row that
            // could be dropped unnoticed.
            new Discharges("List.length", """
                    module demo
                    data NonNeg = Int
                        invariant value >= 0
                    behavior howMany : (xs: List<Int>) -> NonNeg constructs NonNeg
                    let howMany (xs) = NonNeg(List.length(xs))
                    """),
            new Discharges("String.length", """
                    module demo
                    data NonNeg = Int
                        invariant value >= 0
                    behavior howLong : (s: String) -> NonNeg constructs NonNeg
                    let howLong (s) = NonNeg(String.length(s))
                    """),
            new Discharges("Set.size", """
                    module demo
                    data NonNeg = Int
                        invariant value >= 0
                    behavior howMany : (xs: Set<Int>) -> NonNeg constructs NonNeg
                    let howMany (xs) = NonNeg(Set.size(xs))
                    """),
            new Discharges("Map.size", """
                    module demo
                    data NonNeg = Int
                        invariant value >= 0
                    behavior howMany : (m: Map<String, Int>) -> NonNeg constructs NonNeg
                    let howMany (m) = NonNeg(Map.size(m))
                    """),

            // A comparison, at each end of the three numbers it answers.
            new Discharges("Int.compare", """
                    module demo
                    data AtLeastMinusOne = Int
                        invariant value >= -1
                    behavior order : (a: Int, b: Int) -> AtLeastMinusOne
                        constructs AtLeastMinusOne
                    let order (a, b) = AtLeastMinusOne(Int.compare(a, b))
                    """),
            new Discharges("Int.compare", """
                    module demo
                    data AtMostOne = Int
                        invariant value <= 1
                    behavior order : (a: Int, b: Int) -> AtMostOne constructs AtMostOne
                    let order (a, b) = AtMostOne(Int.compare(a, b))
                    """),
            new Discharges("Decimal.compare", """
                    module demo
                    data AtLeastMinusOne = Int
                        invariant value >= -1
                    behavior order : (a: Decimal, b: Decimal) -> AtLeastMinusOne
                        constructs AtLeastMinusOne
                    let order (a, b) = AtLeastMinusOne(Decimal.compare(a, b))
                    """),
            new Discharges("Decimal.compare", """
                    module demo
                    data AtMostOne = Int
                        invariant value <= 1
                    behavior order : (a: Decimal, b: Decimal) -> AtMostOne constructs AtMostOne
                    let order (a, b) = AtMostOne(Decimal.compare(a, b))
                    """),

            // The parts a temporal is read out in, each end of each.
            new Discharges("Time.hour", """
                    module demo
                    data NonNeg = Int
                        invariant value >= 0
                    behavior at : (t: Time) -> NonNeg constructs NonNeg
                    let at (t) = NonNeg(Time.hour(t))
                    """),
            new Discharges("Time.hour", """
                    module demo
                    data OfADay = Int
                        invariant value <= 23
                    behavior at : (t: Time) -> OfADay constructs OfADay
                    let at (t) = OfADay(Time.hour(t))
                    """),
            new Discharges("Time.minute", """
                    module demo
                    data NonNeg = Int
                        invariant value >= 0
                    behavior at : (t: Time) -> NonNeg constructs NonNeg
                    let at (t) = NonNeg(Time.minute(t))
                    """),
            new Discharges("Time.minute", """
                    module demo
                    data OfAnHour = Int
                        invariant value <= 59
                    behavior at : (t: Time) -> OfAnHour constructs OfAnHour
                    let at (t) = OfAnHour(Time.minute(t))
                    """),
            new Discharges("Time.second", """
                    module demo
                    data NonNeg = Int
                        invariant value >= 0
                    behavior at : (t: Time) -> NonNeg constructs NonNeg
                    let at (t) = NonNeg(Time.second(t))
                    """),
            new Discharges("Time.second", """
                    module demo
                    data OfAMinute = Int
                        invariant value <= 59
                    behavior at : (t: Time) -> OfAMinute constructs OfAMinute
                    let at (t) = OfAMinute(Time.second(t))
                    """),
            new Discharges("Date.month", """
                    module demo
                    data Positive = Int
                        invariant value >= 1
                    behavior on : (d: Date) -> Positive constructs Positive
                    let on (d) = Positive(Date.month(d))
                    """),
            new Discharges("Date.month", """
                    module demo
                    data OfAYear = Int
                        invariant value <= 12
                    behavior on : (d: Date) -> OfAYear constructs OfAYear
                    let on (d) = OfAYear(Date.month(d))
                    """),
            new Discharges("Date.day", """
                    module demo
                    data Positive = Int
                        invariant value >= 1
                    behavior on : (d: Date) -> Positive constructs Positive
                    let on (d) = Positive(Date.day(d))
                    """),
            new Discharges("Date.day", """
                    module demo
                    data OfAMonth = Int
                        invariant value <= 31
                    behavior on : (d: Date) -> OfAMonth constructs OfAMonth
                    let on (d) = OfAMonth(Date.day(d))
                    """),

            // And the two whose ends are where the calendar stops. The numbers are written out here
            // rather than read from where the declaration reads them: a test that computed its own
            // expectation the way the thing it tests does would agree with a wrong answer.
            // `ADeclaredBoundIsWhereTheCarrierStopsTest` is what holds them to the carrier.
            new Discharges("Date.year", """
                    module demo
                    data AfterTheFirst = Int
                        invariant value >= -999999999
                    behavior on : (d: Date) -> AfterTheFirst constructs AfterTheFirst
                    let on (d) = AfterTheFirst(Date.year(d))
                    """),
            new Discharges("Date.year", """
                    module demo
                    data BeforeTheLast = Int
                        invariant value <= 999999999
                    behavior on : (d: Date) -> BeforeTheLast constructs BeforeTheLast
                    let on (d) = BeforeTheLast(Date.year(d))
                    """),
            new Discharges("DateTime.minutesBetween", """
                    module demo
                    data NoEarlier = Int
                        invariant value >= -1051898399472959
                    behavior apart : (a: DateTime, b: DateTime) -> NoEarlier constructs NoEarlier
                    let apart (a, b) = NoEarlier(DateTime.minutesBetween(a, b))
                    """),
            new Discharges("DateTime.minutesBetween", """
                    module demo
                    data NoLater = Int
                        invariant value <= 1051898399472959
                    behavior apart : (a: DateTime, b: DateTime) -> NoLater constructs NoLater
                    let apart (a, b) = NoLater(DateTime.minutesBetween(a, b))
                    """));

    private static final List<Discharges> CHOOSING = List.of(
            new Discharges("Int.min", """
                    module demo
                    data Bad
                    data NonNeg = Int
                        invariant value >= 0
                    behavior smaller : (a: Int, b: Int) -> NonNeg | Bad constructs NonNeg
                    let smaller (a, b) = {
                        guard a >= 0
                            else Bad
                        guard b >= 0
                            else Bad
                        NonNeg(Int.min(a, b))
                    }
                    """),
            new Discharges("Decimal.min", """
                    module demo
                    data Bad
                    data NonNegD = Decimal
                        invariant value >= 0.0m
                    behavior smaller : (a: Decimal, b: Decimal) -> NonNegD | Bad
                        constructs NonNegD
                    let smaller (a, b) = {
                        guard a >= 0.0m
                            else Bad
                        guard b >= 0.0m
                            else Bad
                        NonNegD(Decimal.min(a, b))
                    }
                    """),
            new Discharges("Int.max", """
                    module demo
                    data NonNeg = Int
                        invariant value >= 0
                    behavior larger : (x: Int) -> NonNeg constructs NonNeg
                    let larger (x) = NonNeg(Int.max(0, x))
                    """),
            new Discharges("Decimal.max", """
                    module demo
                    data NonNegD = Decimal
                        invariant value >= 0.0m
                    behavior larger : (d: Decimal) -> NonNegD constructs NonNegD
                    let larger (d) = NonNegD(Decimal.max(0.0m, d))
                    """),
            new Discharges("Int.clamp", """
                    module demo
                    data Pct = Int
                        invariant value >= 0 && value <= 100
                    behavior score : (x: Int) -> Pct constructs Pct
                    let score (x) = Pct(Int.clamp(0, 100, x))
                    """),
            new Discharges("Decimal.clamp", """
                    module demo
                    data Rate = Decimal
                        invariant value >= 0.0m && value <= 1.0m
                    behavior capped : (d: Decimal) -> Rate constructs Rate
                    let capped (d) = Rate(Decimal.clamp(0.0m, 1.0m, d))
                    """));

    private static final List<Discharges> SHIFTING = List.of(
            new Discharges("Date.addDays", """
                    module demo
                    data Span = { from: Date, to: Date }
                        invariant Date.daysBetween(from, to) >= 0
                    behavior makeSpan : (d: Date) -> Span constructs Span
                    let makeSpan (d) = Span { from = d, to = Date.addDays(1, d) }
                    """),
            new Discharges("DateTime.addMinutes", """
                    module demo
                    data Window = { opens: DateTime, closes: DateTime }
                        invariant DateTime.minutesBetween(opens, closes) >= 30
                    behavior makeWindow : (dt: DateTime) -> Window constructs Window
                    let makeWindow (dt) = Window { opens = dt, closes = DateTime.addMinutes(30, dt) }
                    """),
            new Discharges("DateTime.addHours", """
                    module demo
                    data Window = { opens: DateTime, closes: DateTime }
                        invariant DateTime.minutesBetween(opens, closes) >= 60
                    behavior makeWindow : (dt: DateTime) -> Window constructs Window
                    let makeWindow (dt) = Window { opens = dt, closes = DateTime.addHours(1, dt) }
                    """),
            new Discharges("DateTime.addDays", """
                    module demo
                    data Window = { opens: DateTime, closes: DateTime }
                        invariant DateTime.minutesBetween(opens, closes) >= 1440
                    behavior makeWindow : (dt: DateTime) -> Window constructs Window
                    let makeWindow (dt) = Window { opens = dt, closes = DateTime.addDays(1, dt) }
                    """));

    private static final List<Discharges> READ_AS_THEIR_ARGUMENT = List.of(
            new Discharges("Decimal.fromInt", """
                    module demo
                    data Bad
                    data NonNegD = Decimal
                        invariant value >= 0.0m
                    behavior widen : (n: Int) -> NonNegD | Bad constructs NonNegD
                    let widen (n) = {
                        guard n >= 0
                            else Bad
                        NonNegD(Decimal.fromInt(n))
                    }
                    """));

    private static Set<String> namesOf(List<Discharges> programs) {
        return programs.stream().map(Discharges::operation)
                .collect(Collectors.toCollection(TreeSet::new));
    }

    /** One program per row, counted: a table gaining a second bound for an operation it already has
     * a program for fails this until the new end gets one of its own. */
    @Test
    void everyBoundHasAConstructionThatFiresIt() {
        assertEquals(DischargeRules.boundedRows().stream().sorted().toList(),
                BOUNDED.stream().map(Discharges::operation).sorted().toList());
    }

    @Test
    void everyChoiceHasAConstructionThatFiresIt() {
        assertEquals(new TreeSet<>(DischargeRules.choosingNames()), namesOf(CHOOSING));
    }

    @Test
    void everyShiftHasAConstructionThatFiresIt() {
        assertEquals(new TreeSet<>(DischargeRules.shiftingNames()), namesOf(SHIFTING));
    }

    @Test
    void everyReadThroughHasAConstructionThatFiresIt() {
        assertEquals(new TreeSet<>(DischargeRules.formNames(DefaultStdlib.get())), namesOf(READ_AS_THEIR_ARGUMENT));
    }

    /**
     * Each program, read for what the check actually did rather than for what it did not say.
     *
     * <p>An analysis that fell over reports nothing, and a construction that discharged reports
     * nothing, and the two are one silence at the boundary ({@link InvariantChecker#GAVE_UP}). So a
     * program is held to three things: nothing was given up on, a construction was reached at all,
     * and every construction reached came out proven. Counting warnings alone would pass on a rule
     * that threw on its first call.
     */
    @Test
    void eachRuleDischargesWhatItsProgramNeeds() {
        List<String> carriedNothing = new ArrayList<>();
        List<Discharges> all = new ArrayList<>(BOUNDED);
        all.addAll(CHOOSING);
        all.addAll(SHIFTING);
        all.addAll(READ_AS_THEIR_ARGUMENT);
        for (Discharges one : all) {
            List<Said> said = new ArrayList<>();
            List<GaveUp> gaveUp = new ArrayList<>();
            InvariantChecker.WATCHING = said;
            InvariantChecker.GAVE_UP = gaveUp;
            long warnings;
            try {
                warnings = Compiler.compileWithWarnings(one.module()).warnings().stream()
                        .filter(d -> d.severity() == Severity.WARNING).count();
            } finally {
                InvariantChecker.WATCHING = null;
                InvariantChecker.GAVE_UP = null;
            }
            if (!gaveUp.isEmpty()) {
                carriedNothing.add(one.operation() + " — the analysis stopped at "
                        + gaveUp.get(0).where() + ": " + gaveUp.get(0).why());
            } else if (said.isEmpty()) {
                carriedNothing.add(one.operation() + " — no construction was reached");
            } else if (!said.stream().allMatch(s -> s.verdict() == Verdict.PROVED)) {
                carriedNothing.add(one.operation() + " — " + said.stream()
                        .map(s -> s.type() + " " + s.verdict()).toList());
            } else if (warnings > 0) {
                carriedNothing.add(one.operation() + " — " + warnings + " warnings");
            }
        }
        assertEquals(List.of(), carriedNothing,
                "the clause should discharge from what the operation answers, and does not");
    }
}
