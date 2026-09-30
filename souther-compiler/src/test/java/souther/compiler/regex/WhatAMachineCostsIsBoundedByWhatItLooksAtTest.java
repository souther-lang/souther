package souther.compiler.regex;

import org.junit.jupiter.api.Test;
import souther.runtime.StringPattern;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What making, reading and writing a machine costs is bounded by what it looks at, and not by its
 * states alone.
 *
 * <p>A state of a deterministic machine is a row as wide as the symbols it tells apart; a state of
 * a meet is the steps of one side against the other's; a walk over a machine that may be in many
 * states at once looks at all of them per symbol. Each of those is counted where it is looked at
 * ({@link Meter}), and the cases here are the shapes that looked at far more than their states said:
 * a machine within every state limit that nothing stopped.
 *
 * <p>And the limits that answer different questions are held apart where the answer depends on
 * their order: what a reading of the rules gives up on has to be something a class still runs.
 */
class WhatAMachineCostsIsBoundedByWhatItLooksAtTest {

    /** The budgets that bound what a class runs rather than what a reading answers. */
    private static final Set<String> OF_A_RUN = Set.of("OF_A_RUN", "OF_A_DETERMINISTIC_RUN");

    /**
     * Every budget a reading of the rules is given stops short of the machine a class runs.
     *
     * <p>A reading past its budget leaves the question unanswered and the program standing, and a
     * program that stands has to be one a class can run; so between the two there has to be room
     * for a pattern the reading gave up on. Asked of every budget declared, so one added later is
     * held to it without being listed here.
     */
    @Test
    void whatAReadingGivesUpOnIsStillSomethingAClassRuns() throws IllegalAccessException {
        List<String> reaching = new ArrayList<>();
        int readings = 0;
        for (Field field : PatternPlan.Budget.class.getFields()) {
            if (!Modifier.isStatic(field.getModifiers()) || field.getType() != PatternPlan.Budget.class
                    || OF_A_RUN.contains(field.getName())) {
                continue;
            }
            readings++;
            PatternPlan.Budget reading = (PatternPlan.Budget) field.get(null);
            if (reading.mostStates() >= PatternPlan.Budget.OF_A_RUN.mostStates()) {
                reaching.add(field.getName());
            }
        }
        assertEquals(List.of(), reaching);
        assertTrue(readings > 1, "the walk found the readings' budgets: " + readings);
    }

    /**
     * And the characters a class is given for one image never refuse a machine the state limit let
     * through for its size alone: a repetition written out, as long as the limit allows.
     */
    @Test
    void theLongestRepetitionAClassRunsFitsTheImageItIsGiven() {
        int most = PatternPlan.Budget.OF_A_RUN.mostStates();
        PatternMeaning meaning = meaning("a{" + (most - 10) + "}");
        PatternImage.Written image =
                assertInstanceOf(PatternImage.Written.class, PatternImage.of(meaning));
        StringPattern run = StringPattern.of(image.strings());
        assertTrue(run.matches("a".repeat(most - 10)));
        assertFalse(run.matches("a".repeat(most - 11)));
    }

    /**
     * A class written wide and repeated is within every state limit and a great deal of work to make
     * deterministic: each state's row is as wide as the class cuts the symbols. It is refused on
     * that work, as a machine larger than one may be, and refused early.
     */
    @Test
    void aWideClassRepeatedIsRefusedOnTheWorkItsRowsTake() {
        PatternMeaning meaning = meaning(wideClass(3000) + "{2000}");
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

    /** A class is read in time its length sets, and not the square of it. */
    @Test
    void aLongClassIsReadInTimeItsLengthSets() {
        assertTimeoutPreemptively(Duration.ofSeconds(10), () ->
                assertInstanceOf(PatternRead.Read.class, PatternParser.read(wideClass(100_000))));
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

    /** A writer says it is past its limit as it goes, and writes nothing out once it is. */
    @Test
    void aWriterPastItsLimitSaysSoAndWritesNothing() {
        StringPattern.Writer out = new StringPattern.Writer(false, 40);
        int at = out.state(false);
        assertTrue(out.holds());
        for (int i = 0; i < 20 && out.holds(); i++) {
            out.step(at, out.set(new int[] {'a', 'a'}), out.state(false));
        }
        assertFalse(out.holds());
        assertThrows(IllegalStateException.class, out::image);
    }

    private static PatternMeaning meaning(String regex) {
        return ((PatternRead.Read) PatternParser.read(regex)).meaning();
    }

    /** A class of {@code many} characters none of which is beside another, all past the basic
     *  plane so that none is half of a pair. */
    private static String wideClass(int many) {
        StringBuilder out = new StringBuilder("[");
        for (int i = 0; i < many; i++) {
            out.appendCodePoint(0x20000 + 2 * i);
        }
        return out.append(']').toString();
    }
}
