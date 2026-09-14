package souther.compiler.execute.jvm;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;
import souther.compiler.examples.Deadline;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One thing this compiler ships keeps a wait.
 *
 * <p>{@link Deadline} says what a deadline is and not how one is kept, so a second answer to how is
 * a second answer to what the wait counts — and the two would differ where it matters, because what
 * is this compile's own time and what is the caller's world's is decided by the arrangement that
 * services the crossing. A build is not a second answer: it is this one with a hand-off nothing ever
 * reaches.
 *
 * <p>Counted rather than named, and counted from what javac made. What is held is that there is one
 * of them, not that the one there is has a particular name. An arrangement a test puts in place is
 * the test's own and is not counted: only what a compile of this compiler emits is read.
 */
class OneMachineKeepsTheWaitTest {

    @Test
    void thereIsOneOfThem() {
        Set<String> keeping = WhatWasCompiled.implementing(Deadline.class);

        assertEquals(1, keeping.size(), () -> "one machine keeps a wait, and these do: " + keeping);
        assertTrue(keeping.iterator().next()
                        .startsWith("souther.compiler.execute.jvm.JvmDeadlines"),
                () -> "and it is the one this machine's arrangement makes: " + keeping);
    }

    /**
     * And the count above can see one wherever it is written.
     *
     * <p>It reads the types a class is, so it finds every answer that is a class and no answer
     * written as a lambda. Nothing can be written as a lambda here while {@link Deadline} asks for
     * more than one thing — which is what this holds, because an interface narrowed to one would
     * make the count go blind rather than make it wrong.
     */
    @Test
    void andADeadlineCannotBeWrittenAsALambda() {
        long asked = 0;
        for (Method each : Deadline.class.getMethods()) {
            if (Modifier.isAbstract(each.getModifiers())) {
                asked++;
            }
        }

        assertTrue(asked > 1, "a deadline asks for " + asked + ", so one could be a lambda and the"
                + " count of them would not see it");
    }
}
