package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.DeclaredLine;
import souther.compiler.check.InvariantStatementId;
import souther.compiler.check.PartId;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.RuleRef;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Towards;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.Duration;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two spellings of one number are one level, so they are one demand and one debt.
 *
 * <p>A level keeps the spelling the rule was written in, because that is what a report writes back:
 * {@code 0} and {@code 0.00} are two values and one place on the order. Everything that compares
 * levels goes through the order, and a value that <em>holds</em> a level and is compared as a value
 * cannot — a map keyed on a debt asks {@link Object#equals}, and a check that two readings ask the
 * same thing asks it of two criteria. Those readers hold the level written the one way.
 *
 * <p>What this is for is the check itself. Two readings of one line that disagree about what a point
 * asks for say the identity that put them together is wrong, and that is only worth acting on where
 * a disagreement is one: over a spelling it names a defect that is not there.
 */
class TwoSpellingsOfOneLevelAreOneDemandTest {

    private static final Carrier DECIMALS = new Carrier.Dense();

    /** A level of {@code DECIMALS} at the number {@code at} is written with. */
    private static Level at(String at) {
        return new Level.OnACarrier(DECIMALS, new Count(new BigDecimal(at)));
    }

    /**
     * The two spellings are two values here, which is what the projection exists for.
     *
     * <p>Asserted rather than assumed: were the records themselves to fold the two, everything below
     * would pass without anything having been asked.
     */
    @Test
    void aLevelKeepsTheSpellingItsRuleWasWrittenIn() {
        assertNotEquals(at("0"), at("0.00"),
                "a level is written back as the author wrote it, so the two are two values");
        assertEquals(at("0").canonical(), at("0.00").canonical(),
                "and they are one place on the order");
    }

    /** Two orders' levels are not one level, whatever the number is written as. */
    @Test
    void aLevelOfAnotherCarrierIsAnotherLevel() {
        Level onWhole = new Level.OnACarrier(new Carrier.Whole(), new Count(BigDecimal.ZERO));
        assertNotEquals(at("0").canonical(), onWhole.canonical(),
                "one number on two orders is two levels");
        assertNotEquals(at("0").canonical(),
                Level.OfTheQuantity.of(0).canonical(),
                "and a number the quantity counts to is on no carrier at all");
        assertEquals(at("0").key(), onWhole.key(),
                "which the key does not tell apart, being about the place alone");
    }

    /** One demand asked at two readings, each spelling its level its own way. */
    @Test
    void twoSpellingsOfOnePointAreOneDemand() {
        Demand asked = new Demand.Owed(new Criterion.AtTheLevel(at("0")));
        Demand also = new Demand.Owed(new Criterion.AtTheLevel(at("0.00")));

        assertNotEquals(asked, also, "two values, so the derived equality has them apart");
        assertTrue(asked.sameAs(also), "and one row answers both, so they are one demand");
    }

    /** And two demands that differ in what they ask are still two. */
    @Test
    void twoPointsAtTwoLevelsAreTwoDemands() {
        Demand asked = new Demand.Owed(new Criterion.AtTheLevel(at("0")));
        Demand other = new Demand.Owed(new Criterion.AtTheLevel(at("1")));

        assertFalse(asked.sameAs(other), "a row at zero is no row at one");
        assertFalse(asked.sameAs(new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT)),
                "and a point nobody is owed a row at is not a point asking for one");
    }

    /** A run written two ways is one run, and two runs that start apart are two. */
    @Test
    void aRunIsToldByWhereItStartsAndNotByWhatItsFirstValueIs() {
        Criterion from0 = run("0", "10");
        Criterion from0Again = run("0.00", "10.0");
        Criterion from5 = run("5", "10");

        assertTrue(from0.sameAs(from0Again), "one run, spelled two ways");
        assertFalse(from0.sameAs(from5), "and a run starting at five is another run");
        assertEquals(band("0", "10").key(), band("5", "10").key(),
                "which the run's own key does not tell apart: over the decimals neither has a"
                        + " first value, and the key is read off the values at the ends");
    }

    /** A debt keyed on a level is keyed on the level and not on how it was written. */
    @Test
    void twoSpellingsOfOneLineAreOneDebt() {
        BorderObligationId one = new BorderObligationId(aLine(), at("0"));
        BorderObligationId same = new BorderObligationId(aLine(), at("0.00"));

        assertEquals(one, same, "one line at one place is one debt");
        assertEquals(one.hashCode(), same.hashCode(), "and a map of debts finds it there");
        assertNotEquals(one, new BorderObligationId(aLine(), at("1")),
                "while the same rule cutting at another place is another debt");
    }

    /** A line at a third and one at two sixths fall in one place, so they are one debt. */
    @Test
    void oneLineWrittenInTwoUnitsIsOneDebt() {
        CutPosition third = new CutPosition(Level.OfTheQuantity.of(1),
                ExactRatio.of(3));
        CutPosition twoSixths = new CutPosition(Level.OfTheQuantity.of(2),
                ExactRatio.of(6));

        assertEquals(third.key(), twoSixths.key(), "which is what the key already said");
        assertEquals(third.canonical(), twoSixths.canonical(), "and now what the value says");
    }

    /**
     * A line a compact decimal puts at a third of a millionth is named and measured without either
     * being written out.
     *
     * <p>Both are questions the size answers and neither is about digits: a name tells two lines
     * apart, and a count of places says how far into a decimal a search has to look. Worked out by
     * forming the number instead, naming such a line spelled a millionth and measuring the distance
     * to another built a whole number of about as many digits as the count it was measured for —
     * which is the work a compact decimal was held compactly to avoid.
     */
    @Test
    void aLineAtAThirdOfAMillionthIsNamedAndMeasuredWithoutBeingWrittenOut() {
        ExactRatio aMillionth = ExactRatio.of(new BigDecimal(BigInteger.ONE, 1_000_000));
        CutPosition line = new CutPosition(new Level.OfTheQuantity(aMillionth), ExactRatio.of(3));
        CutPosition beside = new CutPosition(new Level.OfTheQuantity(aMillionth), ExactRatio.of(6));

        assertTimeoutPreemptively(Duration.ofSeconds(10), () -> {
            assertTrue(line.key().length() < 128, () -> "a name of " + line.key().length());
            assertNotEquals(line.key(), beside.key(), "two lines, two names");
            assertEquals(line.key(), new CutPosition(
                            new Level.OfTheQuantity(aMillionth), ExactRatio.of(3)).key(),
                    "and one line, one name");
            assertTrue(line.digitsToTellApartFrom(beside) > 1_000_000,
                    "a sixth of a millionth apart takes about that many places to name");
        });
    }

    /**
     * A line at a decimal written at a wide scale is named, and so is the division it makes, without
     * either writing the number out.
     *
     * <p>A carrier hands back a count that holds the scale the model wrote and a single digit under
     * it, and what a name is asked for is which of two lines this is — which the parts the count is
     * already held as answer. Built by writing the number instead, a name is a character per place,
     * and a name is wanted wherever two lines meet.
     *
     * <p>What a reader is shown is the other question, and it still writes every place. Asserted
     * here, because a name that stopped costing them by no longer being able to say them is not what
     * this asks for.
     */
    @Test
    void aLineAtADecimalWrittenAtAWideScaleIsNamedWithoutBeingWrittenOut() {
        BigDecimal wide = new BigDecimal(BigInteger.ONE, 1_000_000);
        Level line = new Level.OnACarrier(DECIMALS, new Count(wide));
        Level beside = new Level.OnACarrier(DECIMALS, new Count(wide.add(wide)));
        Level counted = new Level.OfTheQuantity(ExactRatio.of(wide));

        assertEquals("1;1000000", line.key(), "the name is the two parts of the decimal");
        assertNotEquals(line.key(), beside.key(), "two lines, two names");
        assertEquals(line.key(), new Level.OnACarrier(DECIMALS, new Count(wide)).key(),
                "and one line, one name");
        assertEquals(ExactRatio.of(wide).key(), counted.key(),
                "a number the quantity counts to is named by the ratio's own name");
        assertTrue(Seam.of(LevelSpace.onACarrier(DECIMALS), line, Towards.BELOW)
                        .key().length() < 128,
                "and the division that line makes is named from the same parts");

        assertEquals(1_000_002, line.spelled().length(),
                "while what a reader is shown is the number, every place of it");
    }

    /** Two spellings of one number are one name, which is the whole of what a name is for here. */
    @Test
    void twoSpellingsOfOneNumberAreOneName() {
        assertEquals(new Count(new BigDecimal("1.0")).key(), new Count(new BigDecimal("1.00")).key(),
                "1.0 and 1.00 are one place and one name for it");
        assertEquals(new Count(new BigDecimal("0.00")).key(), new Count(BigDecimal.ZERO).key());
        assertNotEquals(new Count(BigDecimal.ONE).key(), new Count(BigDecimal.TEN).key(),
                "and two places are two names");
        assertEquals("1;-1000000", new Count(new BigDecimal(BigInteger.ONE, -1_000_000)).key(),
                "a decimal written as a multiple of a wide power of ten is named the same way");
    }

    /**
     * A level is asked three questions and answers each one its own way: a name, its coordinate,
     * and what an author reads.
     *
     * <p>A division of a quantity is spelled from coordinates, which is the column a report has
     * always carried for it; a level a report shows is written as its carrier writes it, which is
     * what the report's schema says of one.
     */
    @Test
    void aLevelIsNamedSpelledAndWrittenAsThreeDifferentQuestions() {
        Carrier days = new Carrier.Days();
        Level day = new Level.OnACarrier(days, Count.of(20454));

        assertEquals("20454", day.spelled(), "the coordinate is the day count");
        assertEquals("2026-01-01", day.written(), "and what an author reads is the date");
        assertEquals(days.written(Count.of(20454)), day.written(),
                "which is what the carrier says of that place");
        assertEquals("20454|20455", Seam.of(LevelSpace.onACarrier(days), day, Towards.BELOW)
                        .spelled(),
                "and the division of the days is spelled from the counts either side of it");
        assertEquals("7", Level.OfTheQuantity.of(7).written(),
                "a level of no carrier is the number in both");
    }

    /**
     * A level of an enumeration is written as the case it is and spelled as the place the case
     * stands at, so the report shows a name a model contains and not a count it does not.
     */
    @Test
    void aLevelOfAnEnumerationIsWrittenAsItsCase() {
        Carrier colours = new Carrier.Ordinal(
                TypeSymbols.declared(new TypeKey("demo", "Colour")),
                List.of(TypeSymbols.declared(new TypeKey("demo", "Red")),
                        TypeSymbols.declared(new TypeKey("demo", "Blue"))));
        Level blue = new Level.OnACarrier(colours, Count.of(1));

        assertEquals("1", blue.spelled(), "the coordinate is the place the case stands at");
        assertEquals(colours.written(Count.of(1)), blue.written(), "and what an author reads is");
        assertNotEquals(blue.spelled(), blue.written(), "the case, which is not a number");
    }

    /**
     * Where a division is written for a report, and what a name of it costs, is the same whichever
     * way the quantity counts.
     *
     * <p>Spelled from the ratio's own decimal where it has one, as every other number a report
     * writes is, and as a fraction where it has none.
     */
    @Test
    void aDivisionOfNumbersThatCarryNoOrderIsSpelledAsTheNumbers() {
        CutPosition half = CutPosition.at(new Level.OfTheQuantity(
                ExactRatio.of(new BigDecimal("0.5"))));
        Seam belowOnly = new Seam(half, new Level.OfTheQuantity(ExactRatio.of(new BigDecimal("0.5"))),
                null);
        Seam nowhere = new Seam(new CutPosition(new Level.OfTheQuantity(ExactRatio.of(1)),
                ExactRatio.of(3)), null, null);

        assertEquals("0.5|", belowOnly.spelled(), "a half is written as the decimal it is");
        assertEquals("@1/3", nowhere.spelled(), "a third has no decimal and is written as one over three");
        assertNotEquals(belowOnly.spelled(), belowOnly.key(), "and neither is the name");
        assertNotEquals(nowhere.spelled(), nowhere.key());
    }

    /** The run between two levels of {@code DECIMALS}, without the value it is named for. */
    private static Criterion run(String from, String to) {
        return new Criterion.Within(band(from, to), null, Towards.ABOVE);
    }

    private static Band band(String from, String to) {
        return new Band(new BandEnd.AtDomain(new Bound(CutPosition.at(at(from)), false)),
                new BandEnd.AtDomain(new Bound(CutPosition.at(at(to)), false)));
    }

    /** One clause of one declaration, which is only an identity here. */
    private static AuthoredLine aLine() {
        return new AuthoredLine(
                new WhichLine.OfADeclarationsLine(new DeclaredLine.OfAStatement(new InvariantStatementId(
                        new PartId<>(new RuleRef.Invariant(new Clause.Ref(
                                new Clause.Id(
                                        TypeSymbols.declared(
                                                new TypeKey("example.probe", "Amount")), 0),
                                Optional.of(new ClauseName("floor")))), 0),
                        0))),
                new LineFacts(new ComparisonClaim.Cut(Towards.ABOVE, true)), List.of());
    }
}
