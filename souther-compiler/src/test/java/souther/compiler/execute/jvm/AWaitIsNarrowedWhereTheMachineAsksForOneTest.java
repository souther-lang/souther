package souther.compiler.execute.jvm;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;

import java.time.Duration;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A wait is a length wherever this compiler holds one, and becomes a number in one place.
 *
 * <p>The policy admits any positive length, and both ends of that have their own way of being lost:
 * a wait handed on as a number of milliseconds is rounded to none below one, and a wait converted
 * to a number of nanoseconds does not fit at all past what a {@code long} holds. Every place that
 * turns a wait into one of those numbers is a place either can happen, which is why the set of them
 * is worth knowing rather than the places one is known to have happened.
 *
 * <p>So the set is read off what javac made rather than looked for. What is pinned is that it is the
 * two below: a machine that keeps a wait asks its own clock in that clock's units, and a setting
 * that states one in milliseconds is read as milliseconds. Anything else is a length being narrowed
 * where nothing made it necessary, and is the shape of two defects this reading has already had.
 */
class AWaitIsNarrowedWhereTheMachineAsksForOneTest {

    /**
     * Where a length becomes a number, and why each of them may.
     *
     * <p>{@code Handoff} waits on a condition, which is asked for nanoseconds and cannot be asked
     * for a length; what does not fit in one is waited out in as many as it takes, so the number is
     * a piece of the wait and never the whole of it. {@code EvaluationPolicy} reads a setting whose
     * name says milliseconds, and reads its own default back in the same unit to fall back to.
     */
    private static final Set<String> MAY = Set.of(
            "souther.compiler.execute.jvm.Handoff",
            "souther.compiler.execute.EvaluationPolicy");

    @Test
    void onlyTheseTurnALengthIntoANumber() {
        Set<String> narrowing = new TreeSet<>(WhatWasCompiled.callersOf(Duration.class, "toNanos"));
        narrowing.addAll(WhatWasCompiled.callersOf(Duration.class, "toMillis"));

        assertEquals(new TreeSet<>(MAY), narrowing,
                "a wait is a length until the machine that keeps it asks for a number");
    }
}
