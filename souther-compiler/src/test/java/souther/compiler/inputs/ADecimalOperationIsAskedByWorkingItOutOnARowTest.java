package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.DecimalOperation.Formed;
import souther.compiler.inputs.DecimalOperation.Worked;
import souther.compiler.inputs.DecimalOperation.Written;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.BinOp;
import souther.exact.ExactDecimals;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a program gets past a decimal operation is what the run time says of the operation on
 * the row's own values, and not a region of the numbers its operands come to: nought written at
 * the scale of the greatest {@code int} is the number nought, and its product with four has no
 * room.
 */
class ADecimalOperationIsAskedByWorkingItOutOnARowTest {

    private static final BigDecimal FOUR = new BigDecimal("4.0");
    private static final BigDecimal NOUGHT_AT_THE_FLOOR =
            new BigDecimal(BigInteger.ZERO, Integer.MAX_VALUE);

    /** {@code h * 4.0}, with {@code h} the number the key {@code "h"} stands at. */
    private static final DecimalOperation TIMES_FOUR = new DecimalOperation(BinOp.MUL,
            List.of(new Formed(Map.of("h", ExactRatio.ONE), ExactRatio.ZERO), new Written(FOUR)),
            List.of());

    private static boolean completesAt(ExactRatio h, DecimalWork... operations) {
        return DecimalOperation.allCompleteAt(List.of(operations), Map.of("h", h));
    }

    /** The numbers a row is built with, from both ends of the places it is built at and between,
     *  as the builder writes them. */
    private static final List<BigDecimal> ELEMENTS = Stream.of(
                    BigDecimal.ONE.scaleByPowerOfTen(DecimalOperation.PLACES_A_ROW_IS_BUILT_AT),
                    BigDecimal.ONE.scaleByPowerOfTen(-DecimalOperation.PLACES_A_ROW_IS_BUILT_AT),
                    new BigDecimal("-7"), new BigDecimal("123.45"), BigDecimal.ZERO)
            .map(each -> DecimalOperation.writtenForARow(ExactRatio.of(each)))
            .map(written -> ((ExactAnswer.Held<Optional<BigDecimal>>) written).value()
                    .orElseThrow())
            .toList();

    /** Every list of up to three of {@link #ELEMENTS}. */
    private static List<List<BigDecimal>> listsOfElements() {
        List<List<BigDecimal>> lists = new ArrayList<>();
        lists.add(List.of());
        for (int length = 1; length <= 3; length++) {
            List<List<BigDecimal>> longer = new ArrayList<>();
            for (List<BigDecimal> shorter : lists) {
                if (shorter.size() == length - 1) {
                    for (BigDecimal each : ELEMENTS) {
                        List<BigDecimal> grown = new ArrayList<>(shorter);
                        grown.add(each);
                        longer.add(grown);
                    }
                }
            }
            lists.addAll(longer);
        }
        return lists;
    }

    /** What the run time's walk adding {@code elements} to {@code seed} one at a time answers, or
     *  null where a step has no room. */
    private static BigDecimal walked(BigDecimal seed, List<BigDecimal> elements) {
        BigDecimal answer = seed;
        for (BigDecimal each : elements) {
            answer = ExactDecimals.sumWhereThereIsRoom(answer, each);
            if (answer == null) {
                return null;
            }
        }
        return answer;
    }

    /** The total of {@code elements}, the number a row holds at the term the walk adds up. */
    private static Map<Object, ExactRatio> totalOf(List<BigDecimal> elements) {
        return Map.of("t", ExactRatio.of(elements.stream().reduce(BigDecimal.ZERO,
                BigDecimal::add)));
    }

    /**
     * Where the walk is shown to complete on a row, the run time gets through every step of it on
     * every list the row could be built with: the claim is of the steps, and each list's steps are
     * worked out here one at a time, as the run time works them out.
     */
    @Test
    void aWalkShownToCompleteGetsThroughEveryStepOnEveryListARowIsBuiltWith() {
        for (BigDecimal seed : List.of(BigDecimal.ZERO, new BigDecimal("0.0"),
                new BigDecimal("-1.5"), ELEMENTS.get(0), ELEMENTS.get(1))) {
            DecimalAdditiveWalk walk = new DecimalAdditiveWalk(seed, "t");
            for (List<BigDecimal> elements : listsOfElements()) {
                if (DecimalOperation.allCompleteAt(List.of(walk), totalOf(elements))) {
                    assertNotNull(walked(seed, elements), () -> seed + " " + elements);
                }
            }
            assertTrue(DecimalOperation.allCompleteAt(List.of(walk),
                    totalOf(List.of(ELEMENTS.get(0), ELEMENTS.get(1)))), seed::toString);
        }
    }

    /**
     * A seed at a scale room is not shown for is no row, though the seed and the total added once
     * have room: the list that comes to nought is added a step at a time, and the run time stops
     * at its first step.
     */
    @Test
    void aWalkFromASeedAtAScaleNoRoomIsShownForIsNoRow() {
        DecimalAdditiveWalk walk = new DecimalAdditiveWalk(NOUGHT_AT_THE_FLOOR, "t");
        List<BigDecimal> elements = List.of(ELEMENTS.get(0), ELEMENTS.get(0).negate());
        assertNotNull(ExactDecimals.sumWhereThereIsRoom(NOUGHT_AT_THE_FLOOR, BigDecimal.ZERO));
        assertNull(walked(NOUGHT_AT_THE_FLOOR, elements));
        assertFalse(DecimalOperation.allCompleteAt(List.of(walk), totalOf(elements)));
    }

    /** A walk reads the total the row holds, and a row that holds none is no row of it. */
    @Test
    void aWalkOverATotalTheRowDoesNotNameIsNoRow() {
        DecimalAdditiveWalk walk = new DecimalAdditiveWalk(BigDecimal.ZERO, "t");
        assertFalse(DecimalOperation.allCompleteAt(List.of(walk), Map.of("s", ExactRatio.ONE)));
    }

    /**
     * What a walk answers is at the scale its list is written at, which is no fact of the total:
     * an operation worked out of it completes on a row only where its room does not turn on that,
     * as one worked out of a total does.
     */
    @Test
    void whatIsWorkedOutOfAWalkIsAskedAsWhatIsWorkedOutOfATotal() {
        DecimalAdditiveWalk walk = new DecimalAdditiveWalk(new BigDecimal("0.0"), "t");
        Map<Object, ExactRatio> total = totalOf(List.of(new BigDecimal("2.5")));
        DecimalOperation timesFour = new DecimalOperation(BinOp.MUL,
                List.of(new Worked(0), new Written(FOUR)), List.of(0));
        DecimalOperation atTheEdge = new DecimalOperation(BinOp.MUL,
                List.of(new Worked(0), new Written(new BigDecimal(BigInteger.ONE, 1 << 27))),
                List.of(0));
        assertTrue(DecimalOperation.allCompleteAt(List.of(walk, timesFour), total));
        assertFalse(DecimalOperation.allCompleteAt(List.of(walk, atTheEdge), total));
    }

    @Test
    void aProductOfANumberARowHasIsWorkedOut() {
        assertTrue(completesAt(ExactRatio.of(42), TIMES_FOUR));
    }

    @Test
    void aNumberNoDecimalWritesIsNoRow() {
        ExactRatio aThird = ExactRatio.ONE.dividedBy(ExactRatio.of(3)).orNull();
        assertFalse(completesAt(aThird, TIMES_FOUR));
    }

    @Test
    void aNumberWrittenAtMorePlacesThanARowIsBuiltAtIsNoRowOfThoseBuilt() {
        ExactRatio tiny = ExactRatio.of(new BigDecimal(BigInteger.ONE,
                DecimalOperation.PLACES_A_ROW_IS_BUILT_AT + 1));
        ExactRatio atTheLimit = ExactRatio.of(new BigDecimal(BigInteger.ONE,
                DecimalOperation.PLACES_A_ROW_IS_BUILT_AT));
        assertFalse(completesAt(tiny, TIMES_FOUR));
        assertTrue(completesAt(atTheLimit, TIMES_FOUR));
    }

    @Test
    void aTermTheRowDoesNotNameIsNoRow() {
        assertFalse(DecimalOperation.allCompleteAt(List.of(TIMES_FOUR), Map.of("s", ExactRatio.ONE)));
    }

    @Test
    void theSameNumberWrittenAtAnotherScaleIsWorkedOutOrNotAsTheRunTimeSays() {
        DecimalOperation written = new DecimalOperation(BinOp.MUL,
                List.of(new Written(BigDecimal.ZERO), new Written(FOUR)), List.of());
        DecimalOperation writtenAtTheFloor = new DecimalOperation(BinOp.MUL,
                List.of(new Written(NOUGHT_AT_THE_FLOOR), new Written(FOUR)), List.of());
        assertEquals(0, BigDecimal.ZERO.compareTo(NOUGHT_AT_THE_FLOOR));
        assertTrue(completesAt(ExactRatio.ZERO, written));
        assertFalse(completesAt(ExactRatio.ZERO, writtenAtTheFloor));
    }

    @Test
    void anOperationIsWorkedOutOnTheScaleTheOneBeforeItLeft() {
        BigDecimal wide = new BigDecimal(BigInteger.ZERO, 1_000_000_000);
        DecimalOperation first = new DecimalOperation(BinOp.MUL,
                List.of(new Written(wide), new Written(wide)), List.of());
        DecimalOperation then = new DecimalOperation(BinOp.MUL,
                List.of(new Worked(0), new Written(new BigDecimal(BigInteger.ZERO, 200_000_000))),
                List.of(0));
        assertTrue(completesAt(ExactRatio.ZERO, first));
        assertFalse(completesAt(ExactRatio.ZERO, first, then));
    }

    @Test
    void aRowIsComputedWhereEveryOperationToldIsWorkedOutAndNowhereElse() {
        Operations told = new Operations(List.of(), List.of(TIMES_FOUR), Told.EVERY);
        RowsComputed rows = RowsComputed.upTo(null).withOperations(told);
        assertTrue(rows.mayStopARow());
        assertTrue(rows.computedAt(() -> Map.of("h", ExactRatio.of(42))));
        assertFalse(rows.computedAt(() -> Map.of()));
        Operations someToldOnly = new Operations(List.of(), List.of(TIMES_FOUR), Told.SOME);
        assertFalse(RowsComputed.upTo(null).withOperations(someToldOnly)
                .computedAt(() -> Map.of("h", ExactRatio.of(42))));
    }
}
