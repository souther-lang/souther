package souther.compiler.regex;

import org.junit.jupiter.api.Test;
import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternMeaning;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the compiler's questions about patterns cost is bounded by what they look at, and not by
 * the states alone.
 *
 * <p>A state of a deterministic machine is a row as wide as the symbols it tells apart; a state of
 * a meet is the steps of one side against the other's; a walk over a machine that may be in many
 * states at once looks at all of them per symbol. Each of those is counted where it is looked at
 * ({@link Meter}), and the cases here are the shapes that looked at far more than their states said:
 * a machine within every state limit that nothing stopped.
 *
 * <p>And the limits that answer different questions are held apart where the answer depends on
 * their order: what a reading of the rules gives up on has to be a pattern the language admits.
 */
class WhatAMachineCostsIsBoundedByWhatItLooksAtTest {

    /**
     * Every budget a reading of the rules is given stops short of the states a pattern may come to.
     *
     * <p>A reading past its budget leaves the question unanswered and the program standing, so
     * between the two there has to be room for a pattern the reading gave up on and the reader
     * admitted. Asked of every budget declared, so one added later is held to it without being
     * listed here, and of the limit as the reader holds it, so a reader that lowered it is caught.
     */
    @Test
    void whatAReadingGivesUpOnIsStillAPatternTheLanguageAdmits() throws IllegalAccessException {
        List<String> reaching = new ArrayList<>();
        int readings = 0;
        for (Field field : PatternPlan.Budget.class.getFields()) {
            if (!Modifier.isStatic(field.getModifiers()) || field.getType() != PatternPlan.Budget.class) {
                continue;
            }
            readings++;
            PatternPlan.Budget reading = (PatternPlan.Budget) field.get(null);
            if (reading.mostStates() >= PatternRead.Limit.MACHINE_STATES.most()) {
                reaching.add(field.getName());
            }
        }
        assertEquals(List.of(), reaching);
        assertTrue(readings > 1, "the walk found the readings' budgets: " + readings);
    }

    /**
     * A chain of characters each of its own is within every state limit and a great deal of work to
     * make deterministic: it is as many classes as it is long, and each state's row is as wide as
     * that. It is refused on that work, as a machine larger than one may be, and refused early.
     */
    @Test
    void aChainOfCharactersEachOfItsOwnIsRefusedOnTheWorkItsRowsTake() {
        StringBuilder chain = new StringBuilder();
        for (int i = 0; i < 8000; i++) {
            chain.appendCodePoint(0x20000 + i);
        }
        PatternMeaning meaning = meaning(chain.toString());
        Meter meter = PatternPlan.Budget.OF_ADMITTED_VALUES.meter();
        assertTimeoutPreemptively(Duration.ofSeconds(30), () ->
                assertNull(PatternPlan.of(meaning).compile(meter)));
        assertEquals(Meter.Stopped.ONE_MACHINE, meter.stoppedBy());
        assertTrue(Automaton.of(meaning, PatternPlan.Budget.OF_ADMITTED_VALUES.meter()) != null,
                "its shape is within the state limit, so what refused it is the work");
    }

    /**
     * A long chain made smallest costs the chain and not its square: telling its states apart used
     * to take a round per state, each round over every state.
     */
    @Test
    void aLongChainIsMadeSmallestInTimeItsLengthSets() {
        assertTimeoutPreemptively(Duration.ofSeconds(10), () ->
                assertTrue(PatternPlan.of(meaning("a{49000}"))
                        .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter()) != null));
    }

    /**
     * A fold walks a subject in every state the machine may be in at once, and a long subject over
     * a wide machine is refused rather than walked: the match is left to the run time, where it is
     * linear in the subject.
     */
    @Test
    void aFoldOverALongSubjectIsLeftToTheRunTime() {
        Recognizer machine = Recognizer.of(meaning("(a?){10000}"),
                PatternPlan.Budget.OF_A_FOLD.meter());
        assertEquals(Optional.empty(),
                machine.accepts("a".repeat(200_000), PatternPlan.Budget.OF_A_FOLD.meter()));
        assertEquals(Optional.of(true), machine.accepts("a".repeat(10),
                PatternPlan.Budget.OF_A_FOLD.meter()));
    }

    private static PatternMeaning meaning(String regex) {
        return ((PatternRead.Read) PatternParser.read(regex)).meaning();
    }
}
