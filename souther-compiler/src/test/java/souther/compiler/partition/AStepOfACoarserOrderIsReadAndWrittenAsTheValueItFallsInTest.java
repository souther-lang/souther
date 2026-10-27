package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.TestDay;
import souther.compiler.ast.Hir;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The day a date-time falls on is a number of the date-time, read off the second it stands at and
 * written as the first second of the day asked for.
 *
 * <p>The unit is the declaration's ({@code CountsTheWholeUnitsOf}), so nothing here names
 * {@code toDate} except to pick an operation that declares one. The places that tell flooring from
 * truncating are the seconds before the epoch, where the truncated quotient of minus one over a day
 * is nought and the day it falls on is the one before.
 */
class AStepOfACoarserOrderIsReadAndWrittenAsTheValueItFallsInTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final RuleReadingSource RULES = RuleReadings.ofNoClauseFiled(SYMBOLS);
    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            souther.compiler.values.AsACompilationAllows.admittedValues(),
            souther.compiler.values.AsACompilationAllows.whatARuleLeaves());
    private static final RuleReadingContext READING =
            RuleReadingContext.unshared(RULES, POLICY, TestDay.TODAY);
    private static final TermPath AT = TermPath.of("t");
    private static final ValueName.Stdlib TO_DATE = ValueName.Stdlib.operation("DateTime", "toDate");

    private static NumericTerm.WholeUnitsOf theDay() {
        NumericTerm.WholeUnitsOf day = NumericTerm.WholeUnitsOf.of(TO_DATE, AT, Type.Prim.DATETIME,
                ScopedDeclarations.wrapsOf(SYMBOLS), ScopedDeclarations.accessOf(SYMBOLS));
        assertNotNull(day, "toDate counts the days of the date-time it is given");
        return day;
    }

    private static TermOrders orders() {
        return TermOrdersFixtures.at(theDay(), Type.Prim.DATETIME, SYMBOLS);
    }

    private static Place dayOf(String isoDateTime) {
        return assertInstanceOf(NumericTerm.Reading.Number.class,
                orders().read(new ObservedValue.Temporal(isoDateTime))).value();
    }

    /** The unit comes from the declaration, and a day is eighty-six thousand four hundred seconds. */
    @Test
    void theUnitIsWhatTheOperationDeclares() {
        assertEquals(86400, theDay().perUnit());
    }

    /** A second of a day falls in that day, from its first second to its last. */
    @Test
    void everySecondOfADayIsInThatDay() {
        assertEquals(Count.of(0), dayOf("1970-01-01T00:00:00"));
        assertEquals(Count.of(0), dayOf("1970-01-01T23:59:59"));
        assertEquals(Count.of(1), dayOf("1970-01-02T00:00:00"));
        assertEquals(Count.of(20388), dayOf("2025-10-27T12:00:00"));
    }

    /** Floored and not truncated: the second before the epoch is in the day before it. */
    @Test
    void aSecondBeforeTheEpochIsInTheDayBeforeIt() {
        assertEquals(Count.of(-1), dayOf("1969-12-31T23:59:59"));
        assertEquals(Count.of(-1), dayOf("1969-12-31T00:00:00"));
        assertEquals(Count.of(-2), dayOf("1969-12-30T23:59:59"));
    }

    /** What is written for a day reads back as that day, on both sides of the epoch. */
    @Test
    void aValueWrittenForADayReadsBackAsThatDay() {
        TermOrders orders = orders();
        for (long day : new long[] {-719162, -365, -2, -1, 0, 1, 365, 20388, 2932896}) {
            TermRealizations.Realization made = TermRealizations.at(Type.Prim.DATETIME, orders,
                    Count.of(day), NothingTheRulesSay.REGION, READING);
            TermRealizations.Realization.Built built = assertInstanceOf(
                    TermRealizations.Realization.Built.class, made,
                    "some date-time falls on day " + day + ", so there is one to offer");
            for (FixtureTemplate value : built.values()) {
                assertEquals(new NumericTerm.Reading.Number(Count.of(day)),
                        orders.read(temporal(value)),
                        value.text() + " was written for day " + day
                                + " and does not read back as it");
            }
        }
    }

    /** A day past the dates the language holds has no date-time to fall on it. */
    @Test
    void aDayPastTheLastDateIsOneNoDateTimeFallsOn() {
        TermRealizations.Realization made = TermRealizations.at(Type.Prim.DATETIME, orders(),
                Count.of(365_241_780_472L), NothingTheRulesSay.REGION, READING);
        assertTrue(!(made instanceof TermRealizations.Realization.Built),
                "the day after the last date has no value to write");
    }

    /** A call of a unit-counting operation on a position is the term for that position. */
    @Test
    void theTermIsOfThePositionAndOfTheOperation() {
        NumericTerm.WholeUnitsOf there = theDay();
        assertEquals(TO_DATE, there.operation());
        assertEquals(AT, there.position());
        assertNull(NumericTerm.WholeUnitsOf.of(TO_DATE, AT, Type.Prim.DATE,
                ScopedDeclarations.wrapsOf(SYMBOLS), ScopedDeclarations.accessOf(SYMBOLS)),
                "a date has no seconds to count the days of");
        assertNull(NumericTerm.WholeUnitsOf.of(ValueName.Stdlib.operation("DateTime", "toTime"), AT,
                Type.Prim.DATETIME, ScopedDeclarations.wrapsOf(SYMBOLS),
                ScopedDeclarations.accessOf(SYMBOLS)),
                "an operation that declares no unit counts none");
    }

    /**
     * A staleness rule over the date a date-time falls on is read as a relation of the three
     * positions, as the same rule over a date is.
     */
    @Test
    void aStalenessRuleOverTheDayADateTimeFallsOnIsReadLikeOneOverADate() {
        List<String> overDateTime = said(measured("""
                module w1
                behavior m : (t: DateTime, today: Date, after: Int) -> Bool
                let m (t, today, after) = Date.daysBetween(DateTime.toDate(t), today) >= after
                """));
        assertEquals(3, overDateTime.size());
        assertTrue(overDateTime.stream().allMatch(line -> line.startsWith("· no line:")),
                "every position is a relation's and none is a stop: " + overDateTime);
        assertTrue(overDateTime.stream().anyMatch(line -> line.endsWith("`DateTime.toDate(t)`")),
                "the line is on the day, not on the seconds: " + overDateTime);
    }

    private static String measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> said(String report) {
        return report.lines().map(String::strip).filter(line -> line.startsWith("· not read")
                || line.startsWith("· no line")).toList();
    }

    /** A built value as a row holds it: the literal the realizer wrote, as the text of a temporal. */
    private static ObservedValue temporal(FixtureTemplate value) {
        Hir.Expr written = value.value();
        if (written instanceof Hir.Apply built && built.args().size() == 1
                && built.args().get(0) instanceof Hir.StringLit iso) {
            return new ObservedValue.Temporal(iso.value());
        }
        throw new IllegalStateException("a date-time is written as the namespace applied to an ISO"
                + " string, and this is " + written);
    }
}
