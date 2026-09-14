package souther.compiler.execute.jvm;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;
import souther.compiler.examples.Answering;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What keeps the wait and where an application is applied are two halves of one arrangement, and one
 * place picks both.
 *
 * <p>A run whose answers come from outside runs the row on a worker of this compile's own and
 * services what the row hands over on the thread that asked. The half that keeps the wait is the
 * deadline; the half the row hands its applications over through is the caller application, and what
 * it reaches is that worker's hand-off. Offered separately, a caller could name one half of each of
 * two arrangements, and what that makes is an application handed to a thread servicing nothing.
 *
 * <p>So neither is offered to whoever binds an instance: a binding says which instance and which
 * behaviors, and the arrangement is settled where the machine that keeps it is.
 *
 * <p>Read from what javac made rather than from the source, so a helper or a lambda in between is
 * still a caller.
 */
class TheWaitAndTheCrossingAreChosenInOnePlaceTest {

    private static final String HERE = "souther.compiler.execute.jvm.JvmExampleRuns";

    @Test
    void anAnswererForASuppliedInstanceIsMadeWhereTheArrangementIs() {
        assertEquals(Set.of(HERE), WhatWasCompiled.callersOf(Answering.class, "bound"));
    }

    @Test
    void andTheCrossingItIsMadeWithComesFromTheSamePlace() {
        assertEquals(Set.of(HERE),
                WhatWasCompiled.callersOf(Handoff.class, "onTheThreadThatAsked"));
    }
}
