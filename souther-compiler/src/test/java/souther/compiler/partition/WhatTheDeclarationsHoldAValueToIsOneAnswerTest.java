package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.DatePartsLeft;
import souther.compiler.check.HeldClass;
import souther.compiler.check.NarrowedBounds;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.check.RuleRef;
import souther.compiler.coverage.Numberings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.AuthoredPointMapping;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Text;
import souther.compiler.numeric.Towards;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.LocalDate;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a value or a run of a position's order is one its declarations refuse is answered in one
 * place ({@link HeldValues}), and asked of it the same way by every reader.
 *
 * <p>The answer and not the readers. Whether a line is drawn, whether a run is a class and whether a
 * border owes a row each read it; the models that show each of them doing so are beside those
 * readers. What is held here is the answer itself — that it refuses exactly what the declarations
 * leave out, that it says nothing it cannot show, and that it is only ever a refusal.
 */
class WhatTheDeclarationsHoldAValueToIsOneAnswerTest {

    private static final Carrier TEXT = new Carrier.Text();
    private static final Carrier WHOLE = new Carrier.Whole();

    /** A position held to {@code "a"} or {@code "b"}. */
    private static final HeldValues TWO_STRINGS = new HeldValues.OfAPosition(TEXT, HeldClass.NONE,
            new ValueSet.Finite(Set.of(new Value.Text("a"), new Value.Text("b"))));

    /** A position held to the multiples of a thousand. */
    private static final HeldValues THOUSANDS = new HeldValues.OfAPosition(WHOLE,
            new HeldClass.OfResidues(
                    new Congruences(BigInteger.ZERO, BigInteger.valueOf(1000))), ValueSet.ANY);

    private static final Carrier DAYS = new Carrier.Days();

    /** A position held to the first of each month. */
    private static final HeldClass FIRST_OF_A_MONTH = new HeldClass.OfDays(
            new DatePartsLeft(Map.of(TakenAs.DatePart.DAY, onlyAt(1))));

    private static final HeldValues FIRSTS =
            new HeldValues.OfAPosition(DAYS, FIRST_OF_A_MONTH, ValueSet.ANY);

    /** A position held away from two. */
    private static final HeldValues NOT_TWO = new HeldValues.OfAPosition(WHOLE, HeldClass.NONE,
            new ValueSet.Cofinite(Set.of(new Value.Number(BigDecimal.valueOf(2)))));

    @Test
    void aValueTheDeclarationsLeaveOutIsRefusedAndOneTheyNameIsNot() {
        assertTrue(TWO_STRINGS.refuses(text("a0")));
        assertFalse(TWO_STRINGS.refuses(text("a")));
        assertTrue(THOUSANDS.refuses(whole(1500)));
        assertFalse(THOUSANDS.refuses(whole(2000)));
        assertTrue(NOT_TWO.refuses(whole(2)));
        assertFalse(NOT_TWO.refuses(whole(3)));
        assertTrue(FIRSTS.refuses(day("2024-05-15")));
        assertFalse(FIRSTS.refuses(day("2024-06-01")));
    }

    /**
     * A run of days the first of no month falls in is one the declarations leave nothing in, and a
     * run reaching into the next month is not — the class is walked over the calendar and not
     * stepped by a fixed number of days, since months are not one length.
     */
    @Test
    void aRunOfDaysHoldingNoFirstOfAMonthIsOneTheyLeaveNothingIn() {
        assertTrue(FIRSTS.leaveNothingIn(between(day("2024-02-01"), day("2024-03-01")), null));
        assertFalse(FIRSTS.leaveNothingIn(new LevelInterval(Bound.at(day("2024-02-01"), false),
                Bound.at(day("2024-03-01"), true)), null));
    }

    /**
     * The members of a run are drawn from the class from the end the item is named for, so a row
     * offered beside a line on the fifteenth of May is the first of June and the first of May, and
     * a twenty-ninth of February is looked for across the years that have one.
     */
    @Test
    void theMembersOfARunAreTheDaysOfTheClassNearestTheLine() {
        assertEquals(List.of(epochDay("2024-06-01"), epochDay("2024-07-01")),
                FIRST_OF_A_MONTH.within(new NumericDomain.Bounds(Endpoint.exclusive(dayCount("2024-05-15")),
                        null), Towards.ABOVE, 2).values());
        assertEquals(List.of(epochDay("2024-05-01"), epochDay("2024-04-01")),
                FIRST_OF_A_MONTH.within(new NumericDomain.Bounds(null,
                        Endpoint.inclusive(dayCount("2024-05-15"))), Towards.BELOW, 2).values());
        HeldClass leapDays = new HeldClass.OfDays(new DatePartsLeft(Map.of(
                TakenAs.DatePart.DAY, onlyAt(29), TakenAs.DatePart.MONTH, onlyAt(2))));
        assertEquals(List.of(epochDay("2028-02-29")),
                leapDays.within(new NumericDomain.Bounds(Endpoint.inclusive(dayCount("2025-01-01")),
                        null), Towards.ABOVE, 1).values());
    }

    private static NumericDomain.Bounds onlyAt(long value) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(value)),
                Endpoint.inclusive(Count.of(value)));
    }

    private static Count dayCount(String iso) {
        return Dates.dayOf(iso);
    }

    private static BigInteger epochDay(String iso) {
        return BigInteger.valueOf(LocalDate.parse(iso).toEpochDay());
    }

    private static Level day(String iso) {
        return new Level.OnACarrier(DAYS, Dates.dayOf(iso));
    }

    /**
     * A run holding none of what the declarations leave is one they leave nothing in, and a run
     * holding one value they leave is not.
     */
    @Test
    void aRunHoldingNoneOfWhatTheyLeaveIsOneTheyLeaveNothingIn() {
        assertTrue(TWO_STRINGS.leaveNothingIn(between(text("a"), text("b")), null));
        assertFalse(TWO_STRINGS.leaveNothingIn(new LevelInterval(Bound.at(text("a"), true),
                Bound.at(text("b"), false)), null));
        assertTrue(THOUSANDS.leaveNothingIn(between(whole(1000), whole(2000)), null));
        assertFalse(THOUSANDS.leaveNothingIn(new LevelInterval(Bound.at(whole(1500), true),
                Bound.at(whole(2000), true)), null));
        assertTrue(NOT_TWO.leaveNothingIn(between(whole(1), whole(3)), null));
    }

    /**
     * And of the run inside where the value runs. A set named by the values it keeps away from
     * leaves a run nothing only where the run has ends to count between, which the range gives it.
     */
    @Test
    void aRunIsAskedOfInsideWhereTheValueRuns() {
        LevelInterval fromTwo = new LevelInterval(Bound.at(whole(2), true), null);
        assertFalse(NOT_TWO.leaveNothingIn(fromTwo, null),
                "everything from two up holds values other than two");
        assertTrue(NOT_TWO.leaveNothingIn(fromTwo, new NumericDomain.Bounds(
                        Endpoint.inclusive(Count.of(1)), Endpoint.inclusive(Count.of(2)))),
                "and from two up to where the value stops holds two alone");
    }

    /**
     * Nothing is said of a level of another order, nor of a quantity that is no position's value.
     *
     * <p>A set of strings put to a whole number says it holds no such value, which would read as a
     * refusal nobody made.
     */
    @Test
    void nothingIsSaidOfALevelTheValuesAreNotOn() {
        assertFalse(TWO_STRINGS.refuses(whole(1)));
        assertFalse(HeldValues.NONE.refuses(text("a0")));
        assertFalse(HeldValues.NONE.leaveNothingIn(between(text("a"), text("b")), null));
    }

    /**
     * A rule naming a value the declarations refuse owes no row at it, the same as a rule ordering
     * the values does at a point they refuse.
     *
     * <p>Such a line is not drawn where a body writes it — the reading that draws lines asks the
     * same answer first — so the border is built here directly. Its point at the line is the value
     * itself and is never moved to one the declarations do leave.
     */
    @Test
    void aValueSingledOutThatTheDeclarationsRefuseOwesNoRowAtIt() {
        HeldValues odd = new HeldValues.OfAPosition(WHOLE, HeldClass.NONE, new ValueSet.Finite(Set.of(
                new Value.Number(BigDecimal.ONE), new Value.Number(BigDecimal.valueOf(3)))));
        assertEquals(new PointAnswer.NotOwed(NotOwedReason.NO_VALUE_CAN_STAND_THERE, List.of()),
                singledAt(2, odd).answers().get(new DomainPoint.AtTheLine()));
        assertEquals(new PointAnswer.AtLine(new Criterion.AtTheLevel(whole(3))),
                singledAt(3, odd).answers().get(new DomainPoint.AtTheLine()));
    }

    private static Border singledAt(int value, HeldValues held) {
        NumericTerm.ValueOf term = new NumericTerm.ValueOf(TermPath.of("c"));
        BoundaryTarget target = BoundaryTarget.at(new BorderQuantity.OfACoordinate("pick", term,
                TermOrdersFixtures.itself(term, WHOLE)), whole(value));
        return Border.at(target, aSingling(), null, held, ExactAnswer.held(List.of()),
                NarrowedBounds.NOTHING);
    }

    /** A body's rule naming a value, which is only an identity here. */
    private static LineOrigin aSingling() {
        SourceConstructOrigin wrote = new SourceConstructOrigin(
                new WrittenOwner.Body("example.pick", "pick"), 1, 0, SourceConstruct.BINARY);
        return new LineOrigin.ComparisonOrigin(
                new LineOrigin.ComparisonOrigin.Read(
                        new RuleRef.Comparison("pick", wrote),
                        new ModelOccurrence(wrote, ExpansionLineage.ORIGINAL),
                        new RuleReportAnchor.ByTheModuleThatWroteIt(),
                        List.of(Numberings.comparison(1, 0)), ElementsMetOn.EVERY,
                        LineOrigin.NOTHING_ON_THE_WAY, Optional.empty()),
                Optional.empty(),
                new LineFacts(new ComparisonClaim.Singled(true)),
                new AuthoredPointMapping.Proven(WrittenLine.THE_COMPARISON,
                        new ComparisonClaim.Singled(true),
                        Derivation.AComparisonRead.Facing.NOTHING_WRITTEN, true));
    }

    private static LevelInterval between(Level low, Level high) {
        return new LevelInterval(Bound.at(low, false), Bound.at(high, false));
    }

    private static Level text(String value) {
        return new Level.OnACarrier(TEXT, Text.of(value));
    }

    private static Level whole(long value) {
        return new Level.OnACarrier(WHOLE, Count.of(value));
    }
}
