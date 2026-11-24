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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Over a type that holds {@code -5} to {@code 4}, the values of one term that some value of its
 * partner is computed with, and the partner's values beside a value of the term, are those found
 * by working every operation out at every pair of values and holding it to the ends.
 *
 * <p>The cases are the branches of the projection and no more. A term weighed by nought to two
 * and a partner weighed by nought, one or minus one give a lower and an upper bound on the
 * partner, or only one, or none; a constant of either sign moves them; a third term held still
 * is put into the constant; and a second operation is what a lower bound of one meets an upper
 * bound of the other in. The partner is written as itself, as the sum and as the difference of
 * the two, which is every way the callers write it. The rows are counted with plain integers, so
 * that the count and the code do not share the account of what a row computed is.
 */
class RowsOfTheTwoAreTheRowsTheOperationsComputeTest {

    private static final int LEAST = -5;
    private static final int GREATEST = 4;
    /** Where the third term is held still: nought would hide its weight. */
    private static final int HELD = 2;
    /** The values of the free variable, and of the term, the count walks. */
    private static final Span FREE = new Span(BigInteger.valueOf(-6), BigInteger.valueOf(6));
    private static final int AROUND = 16;

    /** {@code onAsked * x + onPartner * y + onHeld * h + constant}, held to the ends. */
    private record Op(int onAsked, int onPartner, int onHeld, int constant) {

        boolean getsPast(int x, int y) {
            int at = onAsked * x + onPartner * y + onHeld * HELD + constant;
            return LEAST <= at && at <= GREATEST;
        }

        IntSum sum() {
            Map<Object, ExactRatio> coefs = new LinkedHashMap<>();
            coefs.put("x", ExactRatio.of(onAsked));
            coefs.put("y", ExactRatio.of(onPartner));
            coefs.put("h", ExactRatio.of(onHeld));
            return new IntSum(coefs, ExactRatio.of(constant), BigInteger.valueOf(LEAST),
                    BigInteger.valueOf(GREATEST));
        }
    }

    /** Each operation alone, and beside one that bounds the partner from the other side. */
    private static List<List<Op>> programs() {
        Op other = new Op(1, -1, 1, 0);
        List<List<Op>> out = new ArrayList<>();
        for (int onAsked = -2; onAsked <= 2; onAsked++) {
            for (int onPartner = -1; onPartner <= 1; onPartner++) {
                for (int onHeld : new int[] {-1, 1}) {
                    for (int constant : new int[] {-2, 3}) {
                        Op each = new Op(onAsked, onPartner, onHeld, constant);
                        out.add(List.of(each));
                        out.add(List.of(each, other));
                    }
                }
            }
        }
        return out;
    }

    private static RowsOfTheTwo rowsOf(List<Op> program) {
        return RowsOfTheTwo.of(new Operations(program.stream().map(Op::sum).toList(), Told.EVERY),
                "x", "y", Map.of("h", ExactRatio.of(HELD)));
    }

    private static boolean holds(Span span, int value) {
        BigInteger at = BigInteger.valueOf(value);
        return !span.isEmpty() && (span.low() == null || span.low().compareTo(at) <= 0)
                && (span.high() == null || at.compareTo(span.high()) <= 0);
    }

    @Test
    void theValuesOfTheTermSomePartnerIsComputedWithAreThoseThatAreFoundByWorkingThemOut() {
        Span anywhere = null;
        Span inTheType = new Span(BigInteger.valueOf(LEAST), BigInteger.valueOf(GREATEST));
        int computed = 0;
        for (List<Op> program : programs()) {
            RowsOfTheTwo rows = rowsOf(program);
            for (Frame frame : List.of(Frame.THE_PARTNER, Frame.OF_THE_SUM, Frame.FROM_ABOVE,
                    Frame.FROM_BELOW)) {
                for (Span partners : new Span[] {anywhere, inTheType}) {
                    Span said = rows.askedWhere(frame, FREE, partners);
                    for (int x = -AROUND; x <= AROUND; x++) {
                        boolean found = false;
                        for (int z = -6; z <= 6 && !found; z++) {
                            int y = frame.onAsked() * x + frame.onFree() * z;
                            found = (partners == null || holds(partners, y))
                                    && allGetPast(program, x, y);
                        }
                        int at = x;
                        assertEquals(found, holds(said, x),
                                () -> program + " in " + frame + ", partners " + partners
                                        + ", at " + at + ": " + said);
                        computed += found ? 1 : 0;
                    }
                }
            }
        }
        assertTrue(computed > 0, "no value was ever computed");
    }

    @Test
    void thePartnersBesideAValueOfTheTermAreThoseThatAreFoundByWorkingThemOut() {
        Span inTheType = new Span(BigInteger.valueOf(LEAST), BigInteger.valueOf(GREATEST));
        int computed = 0;
        for (List<Op> program : programs()) {
            RowsOfTheTwo rows = rowsOf(program);
            for (int x = LEAST; x <= GREATEST; x++) {
                Span said = rows.partnersAt(BigInteger.valueOf(x), inTheType);
                for (int y = LEAST; y <= GREATEST; y++) {
                    boolean found = allGetPast(program, x, y);
                    int term = x;
                    int partner = y;
                    assertEquals(found, holds(said, y),
                            () -> program + ", term at " + term + ", partner " + partner + ": "
                                    + said);
                    computed += found ? 1 : 0;
                }
            }
        }
        assertTrue(computed > 0, "no partner was ever computed");
    }

    private static boolean allGetPast(List<Op> program, int x, int y) {
        for (Op each : program) {
            if (!each.getsPast(x, y)) {
                return false;
            }
        }
        return true;
    }

    @Test
    void operationsThatAreNotAllToldOrReadMoreThanTheTwoAndTheOnesHeldStillAreNotRead() {
        List<IntSum> sums = List.of(new Op(1, 1, 1, 0).sum());
        Map<Object, ExactRatio> held = Map.of("h", ExactRatio.ZERO);
        assertNull(RowsOfTheTwo.of(new Operations(sums, Told.SOME), "x", "y", held));
        assertNull(RowsOfTheTwo.of(new Operations(sums, Told.EVERY), "x", "y", Map.of()));
        assertNull(RowsOfTheTwo.of(new Operations(List.of(new Op(1, 2, 0, 0).sum()), Told.EVERY),
                "x", "y", held));
        assertNull(RowsOfTheTwo.of(new Operations(List.of(), Told.EVERY), "x", "y", Map.of()));
    }
}
