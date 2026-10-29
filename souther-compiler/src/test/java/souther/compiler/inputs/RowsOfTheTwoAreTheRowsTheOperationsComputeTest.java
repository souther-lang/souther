package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.RowsOfTheTwo.Frame;
import souther.compiler.inputs.RowsOfTheTwo.Span;
import souther.compiler.inputs.WhatARelationLeavesUndivided.IntSum;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Over a type that holds {@code -5} to {@code 4}, the values of one term that some value of its
 * partner is computed with, and the partner's values beside a value of the term, are those found
 * by working every operation out at every pair of values and holding it to the ends.
 *
 * <p>The operations weigh the term by up to two and the partner by nought, one or minus one, with
 * a third term held still at a value and a constant, one alone and beside others, and the partner
 * is written as itself, as the sum and as the difference of the two.
 */
class RowsOfTheTwoAreTheRowsTheOperationsComputeTest {

    private static final int LEAST = -5;
    private static final int GREATEST = 4;

    private static IntSum sum(int onAsked, int onPartner, int onHeld, int constant) {
        Map<Object, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put("x", ExactRatio.of(onAsked));
        coefs.put("y", ExactRatio.of(onPartner));
        coefs.put("h", ExactRatio.of(onHeld));
        return new IntSum(coefs, ExactRatio.of(constant), BigInteger.valueOf(LEAST),
                BigInteger.valueOf(GREATEST));
    }

    private static boolean getsPast(List<IntSum> sums, int x, int y, int held) {
        Map<Object, ExactRatio> values = Map.of("x", ExactRatio.of(x), "y", ExactRatio.of(y),
                "h", ExactRatio.of(held));
        for (IntSum each : sums) {
            ExactRatio at = each.at(values);
            if (at.compareTo(ExactRatio.of(LEAST)) < 0 || at.compareTo(ExactRatio.of(GREATEST)) > 0) {
                return false;
            }
        }
        return true;
    }

    private static boolean holds(Span span, int value) {
        BigInteger at = BigInteger.valueOf(value);
        return (span.low() == null || span.low().compareTo(at) <= 0)
                && (span.high() == null || at.compareTo(span.high()) <= 0);
    }

    private static Span span(int low, int high) {
        return new Span(BigInteger.valueOf(low), BigInteger.valueOf(high));
    }

    /** One operation alone, and beside each of a few others. */
    private static List<List<IntSum>> programs() {
        List<IntSum> alone = new ArrayList<>();
        for (int onAsked = -2; onAsked <= 2; onAsked++) {
            for (int onPartner = -1; onPartner <= 1; onPartner++) {
                for (int onHeld = -1; onHeld <= 1; onHeld++) {
                    for (int constant : new int[] {-2, 0, 3}) {
                        alone.add(sum(onAsked, onPartner, onHeld, constant));
                    }
                }
            }
        }
        List<IntSum> beside = List.of(sum(1, 1, 0, 0), sum(1, -1, 1, 0), sum(0, 1, 0, 3));
        List<List<IntSum>> out = new ArrayList<>();
        for (IntSum each : alone) {
            out.add(List.of(each));
            for (IntSum other : beside) {
                out.add(List.of(each, other));
            }
        }
        return out;
    }

    @Test
    void theValuesOfTheTermSomePartnerIsComputedWithAreThoseThatAreFoundByWorkingThemOut() {
        int found = 0;
        for (List<IntSum> sums : programs()) {
            for (int held : new int[] {-3, 0, 2}) {
                RowsOfTheTwo rows = RowsOfTheTwo.of(new Operations(sums, Told.EVERY), "x", "y",
                        Map.of("h", ExactRatio.of(held)));
                assertNotNull(rows, "the operations are read: " + sums);
                for (Frame frame : List.of(Frame.THE_PARTNER, Frame.OF_THE_SUM, Frame.FROM_ABOVE,
                        Frame.FROM_BELOW)) {
                    for (Span free : List.of(span(-6, 6), span(-3, 9))) {
                        for (Span partners : new Span[] {null, span(LEAST, GREATEST)}) {
                            Span said = rows.askedWhere(frame, free, partners);
                            for (int x = -20; x <= 20; x++) {
                                boolean computed = false;
                                for (int z = -60; z <= 60 && !computed; z++) {
                                    int y = frame.onAsked() * x + frame.onFree() * z;
                                    computed = holds(free, z)
                                            && (partners == null || holds(partners, y))
                                            && getsPast(sums, x, y, held);
                                }
                                assertEquals(computed, !said.isEmpty() && holds(said, x),
                                        sums + " held at " + held + " in " + frame + ", free "
                                                + free + ", partners " + partners + ", at " + x
                                                + ": " + said);
                                found += computed ? 1 : 0;
                            }
                        }
                    }
                }
            }
        }
        assertTrue(found > 0, "no value was ever computed");
    }

    @Test
    void thePartnersBesideAValueOfTheTermAreThoseThatAreFoundByWorkingThemOut() {
        int found = 0;
        for (List<IntSum> sums : programs()) {
            for (int held : new int[] {-3, 0, 2}) {
                RowsOfTheTwo rows = RowsOfTheTwo.of(new Operations(sums, Told.EVERY), "x", "y",
                        Map.of("h", ExactRatio.of(held)));
                for (int x = LEAST; x <= GREATEST; x++) {
                    Span said = rows.partnersAt(BigInteger.valueOf(x), span(LEAST, GREATEST));
                    for (int y = LEAST; y <= GREATEST; y++) {
                        boolean computed = getsPast(sums, x, y, held);
                        assertEquals(computed, !said.isEmpty() && holds(said, y),
                                sums + " held at " + held + ", term at " + x + ", partner " + y
                                        + ": " + said);
                        found += computed ? 1 : 0;
                    }
                }
            }
        }
        assertTrue(found > 0, "no partner was ever computed");
    }

    @Test
    void operationsThatAreNotAllToldOrReadMoreThanTheTwoAndTheOnesHeldStillAreNotRead() {
        List<IntSum> sums = List.of(sum(1, 1, 1, 0));
        assertNull(RowsOfTheTwo.of(new Operations(sums, Told.SOME), "x", "y",
                Map.of("h", ExactRatio.ZERO)));
        assertNull(RowsOfTheTwo.of(new Operations(sums, Told.EVERY), "x", "y", Map.of()));
        assertNull(RowsOfTheTwo.of(new Operations(List.of(sum(1, 2, 0, 0)), Told.EVERY), "x", "y",
                Map.of("h", ExactRatio.ZERO)));
        assertNull(RowsOfTheTwo.of(new Operations(List.of(), Told.EVERY), "x", "y", Map.of()));
    }
}
