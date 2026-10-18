package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Line;
import souther.compiler.inputs.WhatARelationLeavesUndivided.SettledRun;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Which values of a term settle a relation, asked of where the other terms may lie, and whether
 * every other value of it is shown to leave the relation either way.
 *
 * <p>Each case is a pair, as for what a relation leaves undivided: the relation as it stands, and
 * the one change that moves the answer. A value is settled where everything the others could be is
 * on one side; it is left either way only where some other term is shown to reach both sides.
 */
class ARelationIsSettledOnlyWhereEveryValueTheOthersMayHoldIsOnOneSideTest {

    private static final BigInteger GREATEST_INT = BigInteger.valueOf(Long.MAX_VALUE);

    private static NumericDomain.Bounds run(Long low, Long high) {
        return new NumericDomain.Bounds(low == null ? null : Endpoint.inclusive(Count.of(low)),
                high == null ? null : Endpoint.inclusive(Count.of(high)));
    }

    private static WhatARelationLeavesUndivided.Term<String> term(String place, long weight,
                                                                 NumericDomain.Bounds holds,
                                                                 NumericDomain.Bounds realizes) {
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight), holds,
                realizes, null, true, Granularity.DISCRETE);
    }

    private static WhatARelationLeavesUndivided.Term<String> denseTerm(
            String place, long weight, NumericDomain.Bounds holds, NumericDomain.Bounds realizes) {
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight),
                holds, realizes, null, true, Granularity.DENSE);
    }

    private static Leaves leavesOf(List<WhatARelationLeavesUndivided.Term<String>> terms, int at,
                                   long constant, Rel relation) {
        return WhatARelationLeavesUndivided.leavesOf(terms, at, ExactRatio.of(constant), relation,
                String::equals, (one, other) -> true, Granularity.DISCRETE, GREATEST_INT);
    }

    private static Leaves ofAProduct(NumericDomain.Bounds it, NumericDomain.Bounds other,
                                     NumericDomain.Bounds reached, long level, Rel relation,
                                     boolean apart) {
        return WhatARelationLeavesUndivided.leavesOfAProduct(term("x", 1, it, it),
                term("y", 1, other, reached), ExactRatio.of(level), relation, apart,
                GREATEST_INT);
    }

    private static SettledRun settled(Long from, Long to, boolean holds) {
        return SettledRun.whole(from == null ? null : BigInteger.valueOf(from),
                to == null ? null : BigInteger.valueOf(to), holds);
    }

    private static Leaves.Settled settledIn(Long least, Long greatest, SettledRun... runs) {
        return Leaves.Settled.ofWhole(List.of(runs),
                least == null ? null : BigInteger.valueOf(least),
                greatest == null ? null : BigInteger.valueOf(greatest));
    }

    private static Line line(Rel relation, long at) {
        return new Line(relation, ExactRatio.of(at));
    }

    /**
     * {@code n - len <= 0}, {@code len} from nought on: every {@code n} at or below nought holds
     * it whatever {@code len} is, and from one on {@code len} is either side of it. Where
     * {@code len} may be anything, nothing is on one side, and {@code n} is undivided.
     */
    @Test
    void aValueEveryOtherValueIsOnOneSideOfSettlesTheRelation() {
        Leaves fromNought = leavesOf(List.of(
                term("n", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                term("len", -1, run(0L, null), run(0L, null))), 0, 0, Rel.LE);
        assertEquals(settledIn(null, null, settled(null, 0L, true)), fromNought);
        assertEquals(List.of(line(Rel.LE, 0)), ((Leaves.Settled) fromNought).lines());

        assertEquals(new Leaves.Undivided(), leavesOf(List.of(
                term("n", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                term("len", -1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN)), 0, 0,
                Rel.LE));
    }

    /**
     * {@code x * y >= 1000} with {@code x} at the least value of the type, whose product with minus
     * one passes where the type stops. That the rule fails there with every {@code y} the run can
     * multiply it by is the end of the type, as {@code x < y} fails at the greatest {@code x}, and
     * draws no line: beside the next value up, which minus one takes over the level, and alone,
     * {@code x} is undivided. Where the one pair a run would be settled by is that one, the run
     * stands only past the type, and nothing is shown.
     */
    @Test
    void theLeastValueAloneIsTheEndOfTheTypeAndDrawsNoLine() {
        long least = Long.MIN_VALUE;
        assertEquals(new Leaves.Undivided(), ofAProduct(run(least, least + 1),
                NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN, 1000, Rel.GE, true));
        assertEquals(new Leaves.Undivided(), ofAProduct(run(least, least), run(-1L, 1L),
                run(-1L, 1L), 1000, Rel.GE, true));
        assertNull(ofAProduct(run(least, least), run(-1L, -1L), run(-1L, -1L), 1000, Rel.GE,
                true));
    }

    /**
     * {@code 4 * x + y >= 0}, {@code y} from the least value of the type to ten above it: the
     * values settling it are {@code x} from two to the sixty-first on, and four times any of them
     * passes where the type stops, so no row of that run has a value and it is no class — nothing
     * is shown. With {@code y} from nought to ten the run starts at nought, which has rows.
     */
    @Test
    void aRunWhoseEveryRowPassesWhereTheTypeStopsIsNoClass() {
        long least = Long.MIN_VALUE;
        assertNull(leavesOf(List.of(
                term("x", 4, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                term("y", 1, run(least, least + 10), run(least, least + 10))), 0, 0, Rel.GE));

        Leaves near = leavesOf(List.of(
                term("x", 4, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                term("y", 1, run(0L, 10L), run(0L, 10L))), 0, 0, Rel.GE);
        assertEquals(List.of(settled(null, -3L, false), settled(0L, null, true)),
                ((Leaves.Settled) near).runs());
    }

    /**
     * {@code x + y >= 1000}, each from one to a hundred thousand: from 999 on {@code x} holds it
     * whatever {@code y} is, and below that {@code y} reaches either side. Where {@code y} is
     * shown to reach nothing, the values below are not shown either way, and nothing is answered.
     */
    @Test
    void theValuesLeftBetweenTheSettledRunsAreAskedWhatTheOtherReaches() {
        NumericDomain.Bounds both = run(1L, 100_000L);
        Leaves reached = leavesOf(List.of(term("x", 1, both, both), term("y", 1, both, both)), 0,
                -1000, Rel.GE);
        assertEquals(settledIn(1L, 100_000L, settled(999L, 100_000L, true)), reached);
        assertEquals(List.of(line(Rel.GE, 999)), ((Leaves.Settled) reached).lines());

        assertNull(leavesOf(List.of(term("x", 1, both, both), term("y", 1, both, null)), 0, -1000,
                Rel.GE));
    }

    /**
     * {@code x * y >= 1000} over every whole number: nought fails it whatever {@code y} is, and
     * every other {@code x} leaves {@code y} either side of the level over it. Held away from
     * nought, {@code x} is undivided.
     */
    @Test
    void noughtSettlesAProductWhateverTheOtherFactorIs() {
        Leaves everywhere = ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, 1000, Rel.GE, true);
        assertEquals(settledIn(null, null, settled(0L, 0L, false)), everywhere);
        assertEquals(List.of(line(Rel.EQ, 0)), ((Leaves.Settled) everywhere).lines());

        assertEquals(new Leaves.Undivided(), ofAProduct(run(1L, null), NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, 1000, Rel.GE, true));
    }

    /**
     * Each from one to a hundred thousand: from a thousand on, {@code x} holds it whatever
     * {@code y} is, and below that {@code y} is either side of the level over it. With {@code y}
     * from two, the values from five hundred on hold it.
     */
    @Test
    void aFactorFarEnoughFromNoughtSettlesTheProductAlone() {
        NumericDomain.Bounds both = run(1L, 100_000L);
        Leaves fromOne = ofAProduct(both, both, both, 1000, Rel.GE, true);
        assertEquals(settledIn(1L, 100_000L, settled(1000L, 100_000L, true)), fromOne);
        assertEquals(List.of(line(Rel.GE, 1000)), ((Leaves.Settled) fromOne).lines());

        NumericDomain.Bounds fromTwo = run(2L, 100_000L);
        assertEquals(settledIn(1L, 100_000L, settled(500L, 100_000L, true)),
                ofAProduct(both, fromTwo, fromTwo, 1000, Rel.GE, true));
    }

    /**
     * Which side of the level over a value the other factor has to pass strictly is the one the
     * relation fails on: under {@code x * y >= 10}, {@code x} at one needs a {@code y} below ten
     * and one at ten or above, and {@code y} from five to ten has both, ten at its end. With
     * {@code y} only up to nine it has no value the relation holds at, and {@code x} at one fails
     * it whatever {@code y} is; {@code x} at two holds it either way.
     */
    @Test
    void theOtherFactorPassesTheLevelStrictlyOnlyOnTheSideTheRelationFailsOn() {
        NumericDomain.Bounds oneOrTwo = run(1L, 2L);
        NumericDomain.Bounds toTen = run(5L, 10L);
        assertEquals(settledIn(1L, 2L, settled(2L, 2L, true)),
                ofAProduct(oneOrTwo, toTen, toTen, 10, Rel.GE, true));

        NumericDomain.Bounds toNine = run(5L, 9L);
        assertEquals(settledIn(1L, 2L, settled(1L, 1L, false), settled(2L, 2L, true)),
                ofAProduct(oneOrTwo, toNine, toNine, 10, Rel.GE, true));
    }

    /**
     * {@code x} held at one, {@code y} from minus ten to ten: {@code y} reaches both signs and
     * never a thousand, so the one value of {@code x} fails it whatever {@code y} is. With
     * {@code y} up to two thousand, it is reached either side.
     */
    @Test
    void reachingBothSignsIsNotReachingBothSidesOfTheLevel() {
        NumericDomain.Bounds one = run(1L, 1L);
        NumericDomain.Bounds near = run(-10L, 10L);
        assertEquals(settledIn(1L, 1L, settled(1L, 1L, false)),
                ofAProduct(one, near, near, 1000, Rel.GE, true));

        NumericDomain.Bounds far = run(-2000L, 2000L);
        assertEquals(new Leaves.Undivided(), ofAProduct(one, far, far, 1000, Rel.GE, true));
    }

    /**
     * Where twice the level is past the greatest value of the type, a value the other has to stand
     * at may put the product past it, and nothing is shown. Within it, the product is answered.
     */
    @Test
    void aLevelTooNearTheEndOfTheTypeShowsNothing() {
        assertNull(ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, 5_000_000_000_000_000_000L, Rel.GE, true));
        assertEquals(settledIn(null, null, settled(0L, 0L, false)),
                ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                        NumericDomain.Bounds.OPEN, 4_000_000_000_000_000_000L, Rel.GE, true));
    }

    /**
     * Held equal to a level other than nought, which values of {@code x} leave {@code y} a whole
     * number to stand at is which of them divide the level, and nothing is shown. Against nought,
     * nought holds it and every other {@code x} leaves {@code y} at nought or away from it.
     */
    @Test
    void anEqualityIsAnsweredOnlyAgainstNought() {
        assertNull(ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, 1000, Rel.EQ, true));
        assertEquals(settledIn(null, null, settled(0L, 0L, true)),
                ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                        NumericDomain.Bounds.OPEN, 0, Rel.EQ, true));
    }

    /**
     * Tied to {@code x}, what {@code y} reaches says nothing of the values between the settled
     * ones. A value settled whatever {@code y} is, is settled all the same.
     */
    @Test
    void aTiedFactorShowsOnlyTheValuesSettledWhateverItIs() {
        assertNull(ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, 1000, Rel.GE, false));
        assertEquals(settledIn(0L, 0L, settled(0L, 0L, false)),
                ofAProduct(run(0L, 0L), NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN, 1000,
                        Rel.GE, false));
    }

    /**
     * Two runs settling it opposite ways side by side are parted by one line, and a run of one
     * value with values left either way on both sides is that value singled out. Runs apart are
     * lines apart, and two of one kind on one term stand at different values.
     */
    @Test
    void theLinesPartingTheRunsAreEachOfTheirOwnKind() {
        assertEquals(List.of(line(Rel.LE, 39)),
                settledIn(null, null, settled(null, 39L, false), settled(40L, null, true))
                        .lines());
        assertEquals(List.of(line(Rel.LE, -100), line(Rel.EQ, 0), line(Rel.GE, 100)),
                settledIn(null, null, settled(null, -100L, true), settled(0L, 0L, false),
                        settled(100L, null, true)).lines());
        assertEquals(List.of(line(Rel.GE, 0), line(Rel.LE, 5), line(Rel.GE, 10), line(Rel.LE, 20)),
                settledIn(null, null, settled(0L, 5L, false), settled(10L, 20L, true)).lines());
    }

    private static NumericDomain.Bounds dense(String low, boolean lowIn, String high,
                                              boolean highIn) {
        return new NumericDomain.Bounds(
                new Endpoint(Count.of(new BigDecimal(low)), lowIn),
                new Endpoint(Count.of(new BigDecimal(high)), highIn));
    }

    private static Leaves denseLeavesOf(NumericDomain.Bounds it, NumericDomain.Bounds other,
                                        NumericDomain.Bounds reached, long weight,
                                        Rel relation) {
        return denseLeavesOf(denseTerm("x", 1, it, it), denseTerm("y", weight, other, reached),
                relation);
    }

    private static Leaves denseLeavesOf(WhatARelationLeavesUndivided.Term<String> x,
                                        WhatARelationLeavesUndivided.Term<String> y,
                                        Rel relation) {
        return WhatARelationLeavesUndivided.leavesOf(List.of(x, y), 0, ExactRatio.ZERO, relation,
                String::equals, (one, two) -> true, Granularity.DENSE, null);
    }

    /**
     * {@code x > w} with both between nought and one: nought is settled and a value above it is
     * not, so the one line is {@code x <= 0}, with nought on the settled side. A value just
     * above nought has {@code w} on both sides only because {@code w} takes nought itself, which
     * the run left to ask about does not.
     */
    @Test
    void aDenseTermIsPartedAtTheEndTheOtherTermsRunStopsAt() {
        NumericDomain.Bounds unit = dense("0", true, "1", true);
        Leaves leaves = denseLeavesOf(unit, unit, unit, -1, Rel.GT);
        assertEquals(List.of(line(Rel.LE, 0)), ((Leaves.Settled) leaves).lines());
        assertNull(denseLeavesOf(unit, unit, dense("0.5", true, "1", true), -1, Rel.GT));
    }

    /**
     * {@code x + y < 0} with {@code y} between nought and one, both left out, holds at minus one
     * and fails at nought. Between them {@code y} is on both sides of {@code -x} whatever {@code x}
     * is, though it takes neither end, because a dense term takes values as near an end as asked
     * of.
     */
    @Test
    void aDenseTermTakingAnOpenRunReachesTheValuesInsideItFromBothSides() {
        NumericDomain.Bounds open = dense("0", false, "1", false);
        Leaves leaves = denseLeavesOf(NumericDomain.Bounds.OPEN, open, open, 1, Rel.LT);
        assertEquals(List.of(line(Rel.LE, -1), line(Rel.GE, 0)),
                ((Leaves.Settled) leaves).lines());
    }

    /** A term that is not dense has no value between an end it leaves out and the next, so the
     *  same open run is not one it reaches the values inside from both sides. */
    @Test
    void aTermThatIsNotDenseIsNotTakenAsOneThatTakesValuesNearAnEndItLeavesOut() {
        NumericDomain.Bounds open = dense("0", false, "1", false);
        assertNull(denseLeavesOf(denseTerm("x", 1, NumericDomain.Bounds.OPEN,
                        NumericDomain.Bounds.OPEN), term("y", 1, open, open), Rel.LT));
    }

    /** The same asked at the least end of the run alone: {@code x > y} for {@code y} above nought
     *  up to one, and the values of {@code x} above nought, are reached below by a dense
     *  {@code y} that takes no nought and not by one that is whole. */
    @Test
    void theLeastEndOfAnOpenRunIsReachedByADenseTermAlone() {
        NumericDomain.Bounds unit = dense("0", true, "1", true);
        NumericDomain.Bounds aboveNought = dense("0", false, "1", true);
        Leaves leaves = denseLeavesOf(denseTerm("x", 1, unit, unit),
                denseTerm("y", -1, aboveNought, aboveNought), Rel.GT);
        assertEquals(List.of(line(Rel.LE, 0)), ((Leaves.Settled) leaves).lines());
        assertNull(denseLeavesOf(denseTerm("x", 1, unit, unit),
                term("y", -1, aboveNought, aboveNought), Rel.GT));
    }

    /**
     * {@code 3x - y < 0} with {@code y} from nought to one: {@code x} lies below a third wherever
     * {@code y} is, which no decimal writes. The line is at the third all the same, and the
     * values between nought and it are asked of {@code y} as they are.
     */
    @Test
    void anEndNoDecimalWritesIsStillTheEndOfTheRunAskedAbout() {
        NumericDomain.Bounds aboveNought = new NumericDomain.Bounds(
                Endpoint.exclusive(Count.of(0)), null);
        NumericDomain.Bounds unit = dense("0", true, "1", true);
        Leaves leaves = denseLeavesOf(denseTerm("x", 3, aboveNought, aboveNought),
                denseTerm("y", -1, unit, unit), Rel.LT);
        assertEquals(List.of(new Line(Rel.GE, ExactRatio.of(BigInteger.ONE,
                BigInteger.valueOf(3)))), ((Leaves.Settled) leaves).lines());
    }

    /** Runs a point apart are lines apart: a point both leave out is not covered. */
    @Test
    void aPointNoRunTakesIsAGapBetweenTwoDenseRuns() {
        ExactRatio five = ExactRatio.of(5);
        Leaves.Settled apart = new Leaves.Settled(List.of(
                new SettledRun(null, ExactCut.exclusive(five), true),
                new SettledRun(ExactCut.exclusive(five), null, false)), null, null, false);
        assertEquals(List.of(new Line(Rel.LT, five), new Line(Rel.GT, five)), apart.lines());
        Leaves.Settled touching = new Leaves.Settled(List.of(
                new SettledRun(null, ExactCut.inclusive(five), true),
                new SettledRun(ExactCut.exclusive(five), null, false)), null, null, false);
        assertEquals(List.of(new Line(Rel.LE, five)), touching.lines());
    }
}
