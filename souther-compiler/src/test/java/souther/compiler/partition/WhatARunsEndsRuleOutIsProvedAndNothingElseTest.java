package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run's ends rule out of a relation is a proof, and a run they say nothing about proves
 * nothing.
 *
 * <p>Held against the values themselves rather than against a second table: every run with ends
 * among a few numbers, open or closed or absent, and every relation to each of those numbers, put
 * beside a walk of the numbers on a grid fine enough to witness any value the run holds. Ruled out
 * is never said of a relation some value of the run meets, and a relation no value of a run that
 * holds something meets is ruled out — which is the whole of what the ends can tell.
 */
class WhatARunsEndsRuleOutIsProvedAndNothingElseTest {

    private static final List<BigDecimal> LINES = List.of(
            BigDecimal.valueOf(-1), BigDecimal.ZERO, BigDecimal.ONE);

    /** Every half step from beyond the lowest end to beyond the highest. */
    private static final List<BigDecimal> GRID = grid();

    @Test
    void aRunWithNoEndsProvesNothing() {
        for (NumericDomain.Bounds runs : Arrays.asList(null, NumericDomain.Bounds.OPEN)) {
            for (Rel asked : Rel.values()) {
                assertFalse(WhatTheDeclarationsLeave.ruledOutByBounds(runs, asked,
                        Count.of(0)), () -> asked + " over " + runs);
            }
        }
    }

    @Test
    void whatIsRuledOutIsWhatNoValueOfTheRunMeets() {
        for (NumericDomain.Bounds runs : everyRun()) {
            boolean holdsSomething = GRID.stream().anyMatch(v -> within(runs, v));
            for (BigDecimal line : LINES) {
                for (Rel asked : Rel.values()) {
                    boolean none = GRID.stream()
                            .noneMatch(v -> within(runs, v) && meets(v, asked, line));
                    boolean ruledOut = WhatTheDeclarationsLeave.ruledOutByBounds(runs, asked,
                            Count.of(line));
                    String said = runs + " " + asked + " " + line;
                    if (ruledOut) {
                        assertTrue(none, () -> "ruled out though a value meets it: " + said);
                    }
                    if (holdsSomething) {
                        assertEquals(none, ruledOut, said);
                    }
                }
            }
        }
    }

    /** At the end itself: a closed end holds the line, an open one does not. */
    @Test
    void theLineItselfIsHeldOnlyByAClosedEnd() {
        Count zero = Count.of(0);
        NumericDomain.Bounds closed = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(-1)), Endpoint.inclusive(zero));
        NumericDomain.Bounds open = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(-1)), Endpoint.exclusive(zero));

        assertFalse(WhatTheDeclarationsLeave.ruledOutByBounds(closed, Rel.GE, zero));
        assertTrue(WhatTheDeclarationsLeave.ruledOutByBounds(open, Rel.GE, zero));
        // One value, which an end short of it rules out from one side alone.
        assertTrue(WhatTheDeclarationsLeave.ruledOutByBounds(open, Rel.EQ, zero));
        // Every value but one, which takes both sides being empty of anything else.
        assertFalse(WhatTheDeclarationsLeave.ruledOutByBounds(closed, Rel.NE, zero));
        assertTrue(WhatTheDeclarationsLeave.ruledOutByBounds(
                new NumericDomain.Bounds(Endpoint.inclusive(zero), Endpoint.inclusive(zero)),
                Rel.NE, zero));
    }

    private static List<NumericDomain.Bounds> everyRun() {
        List<Endpoint> ends = new ArrayList<>();
        ends.add(null);
        for (BigDecimal at : LINES) {
            ends.add(Endpoint.inclusive(Count.of(at)));
            ends.add(Endpoint.exclusive(Count.of(at)));
        }
        List<NumericDomain.Bounds> runs = new ArrayList<>();
        for (Endpoint min : ends) {
            for (Endpoint max : ends) {
                runs.add(new NumericDomain.Bounds(min, max));
            }
        }
        return runs;
    }

    private static boolean within(NumericDomain.Bounds runs, BigDecimal v) {
        return beyond(runs.min(), v, false) && beyond(runs.max(), v, true);
    }

    /** Whether {@code v} is on the run's side of {@code end}. */
    private static boolean beyond(Endpoint end, BigDecimal v, boolean isMax) {
        if (end == null) {
            return true;
        }
        int against = v.compareTo(((Count) end.at()).at());
        return against == 0 ? end.inclusive() : isMax ? against < 0 : against > 0;
    }

    private static boolean meets(BigDecimal v, Rel asked, BigDecimal line) {
        int against = v.compareTo(line);
        return switch (asked) {
            case GT -> against > 0;
            case GE -> against >= 0;
            case LT -> against < 0;
            case LE -> against <= 0;
            case EQ -> against == 0;
            case NE -> against != 0;
        };
    }

    private static List<BigDecimal> grid() {
        List<BigDecimal> grid = new ArrayList<>();
        for (int halves = -4; halves <= 4; halves++) {
            grid.add(BigDecimal.valueOf(halves).divide(BigDecimal.valueOf(2)));
        }
        return grid;
    }
}
