package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.carrier.Membership;
import souther.compiler.core.Core;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.check.ElementBindings;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.ValueDefinitions;
import souther.compiler.types.Type;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.ExactRatio;

import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What a value comes to at a reading is worked out once however many statements ask it, and an
 * answer is kept only where taking it again is the same answer.
 */
class WhatANameComesToAtAReadingIsWorkedOutOncePerInputTest {

    private static final FormRange ONE = new FormRange(ExactRatio.ONE, ExactRatio.ONE);

    private static Core value() {
        return new Core.Int(0, Type.INT, new SourcePos(0, 0));
    }

    private static InputReads reading() {
        return InputReads.ofParameters(Map.of(), DeclaredInput.NONE, ElementBindings.NONE,
                ValueDefinitions.NONE, Membership.none());
    }

    @Test
    void theSameValueAtTheSameReadingIsWorkedOutOnce() {
        RangesOfNames names = new RangesOfNames();
        Core value = value();
        InputReads at = reading();
        AtomicInteger worked = new AtomicInteger();

        for (int asked = 0; asked < 3; asked++) {
            assertEquals(ONE, names.of(value, at, () -> {
                worked.incrementAndGet();
                return new Pullback.Spendless<>(ONE, true);
            }));
        }

        assertEquals(1, worked.get());
    }

    @Test
    void theSameValueAtAnotherReadingAndAnotherValueAtTheSameReadingAreWorkedOutApart() {
        RangesOfNames names = new RangesOfNames();
        Core value = value();
        InputReads at = reading();
        AtomicInteger worked = new AtomicInteger();

        names.of(value, at, () -> counted(worked));
        names.of(value, reading(), () -> counted(worked));
        names.of(value(), at, () -> counted(worked));

        assertEquals(3, worked.get());
    }

    @Test
    void anAnswerThatSpentAReadingTheFiguresAllowIsNotKept() {
        RangesOfNames names = new RangesOfNames();
        Core value = value();
        InputReads at = reading();
        AtomicInteger worked = new AtomicInteger();

        for (int asked = 0; asked < 2; asked++) {
            names.of(value, at, () -> {
                worked.incrementAndGet();
                return new Pullback.Spendless<>(ONE, false);
            });
        }

        assertEquals(2, worked.get());
    }

    @Test
    void thatNoNumbersAreKnownIsKeptAsTheNumbersAre() {
        RangesOfNames names = new RangesOfNames();
        Core value = value();
        InputReads at = reading();
        AtomicInteger worked = new AtomicInteger();

        for (int asked = 0; asked < 2; asked++) {
            assertNull(names.of(value, at, () -> {
                worked.incrementAndGet();
                return new Pullback.Spendless<>(null, true);
            }));
        }

        assertEquals(1, worked.get());
    }

    private static Pullback.Spendless<FormRange> counted(AtomicInteger worked) {
        worked.incrementAndGet();
        return new Pullback.Spendless<>(ONE, true);
    }
}
