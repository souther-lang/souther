package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Severity;
import souther.compiler.meta.ModulePath;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What of a module may be run, held against a module one of whose bodies was refused.
 *
 * <p>A behavior's own check says nothing about this. One body is checked against the signatures and
 * the stated relations of what it calls and never against another body, so a behavior calling a
 * refused one checks exactly as it would have — and the call it makes is to a method nothing
 * emitted. So the answer is a closure over what a body reaches, and the test of that is a chain: a
 * caller of the refused body goes, and so does its own caller.
 */
class WhatMayBeRunIsClosedUnderWhatABodyReachesTest {

    /**
     * A chain of callers over a body the invariant refuses, and one behavior off to the side.
     *
     * <p>{@code %s} is what {@code mint} constructs. Written as one model with the construction
     * moved, so the two readings below differ in that and in nothing else.
     *
     * <p><b>The chain is declared against the direction it is read in.</b> Each caller stands
     * before what it calls, so the first walk of the behaviors meets {@code thrice} while
     * {@code twice} is still standing. Declared the other way round, one walk would take the whole
     * chain away and a reading that stopped after one would pass.
     */
    private static final String MODEL = """
            module demo

            data Seat = Int
                invariant value >= 1 && value <= 300

            behavior apart : (n: Int) -> Int
            let apart (n) = n

            behavior thrice : (n: Int) -> Seat
            let thrice (n) = twice(n)

            behavior twice : (n: Int) -> Seat
            let twice (n) = mint(n)

            behavior mint : (n: Int) -> Seat
                constructs Seat
            let mint (n) = Seat(%s)
            """;

    /** What this compiler refuses a construction its own invariant rejects. */
    private static final String THE_REFUSED_CONSTRUCTION = "E2010";

    /**
     * Every body came out, so every one of them may be run.
     *
     * <p>Here so that the reading below is a difference and not a coincidence. Answered {@code
     * apart} alone whatever the model, this would pass with the closure removed and with the whole
     * answer returning one name.
     */
    @Test
    void whereEveryBodyCameOutEveryBehaviorMayBeRun() {
        Compiled clean = compile("1");

        assertTrue(clean.checkedModule(), "this model is written to be a module that emits");
        assertEquals(List.of(), clean.refusals(),
                () -> "nothing is refused about this model, and it was refused about "
                        + clean.refusals());
        assertEquals(Set.of("mint", "twice", "thrice", "apart"), clean.runnable());
    }

    /**
     * One refused body takes its callers with it, and leaves the behavior beside them.
     *
     * <p>The chain is what says this is a closure. {@code twice} calls the refused body and
     * {@code thrice} calls {@code twice}, so an answer that took away only what reaches a refused
     * body directly would keep {@code thrice}.
     */
    @Test
    void aRefusedBodyTakesEveryBehaviorThatReachesIt() {
        Compiled refused = compile("0");

        assertFalse(refused.checkedModule(),
                "this model is written to be a module that does not emit");
        assertEquals(List.of(THE_REFUSED_CONSTRUCTION), refused.refusals(),
                () -> "this model is refused about the construction alone, and it was refused"
                        + " about " + refused.refusals());
        assertEquals(Set.of("apart"), refused.runnable());
    }

    /** A compilation of the model, and the answers this asks of it. */
    private record Compiled(Compilation compilation) {

        Set<String> runnable() {
            Answer<Set<String>> answer =
                    compilation.db().ask(new Bodies.RunnableBehaviors("demo"));
            assertTrue(answer.present(),
                    "a module that settled is one this answers about");
            return answer.value();
        }

        boolean checkedModule() {
            return compilation.db().ask(new Bodies.Checked("demo")).present();
        }

        List<String> refusals() {
            return compilation.diagnostics().values().stream()
                    .flatMap(List::stream)
                    .filter(each -> each.diagnostic().severity() == Severity.ERROR)
                    .map(each -> each.diagnostic().code().toString())
                    .sorted()
                    .toList();
        }
    }

    private static Compiled compile(String constructs) {
        Compilation compilation =
                Compilation.ofSources(List.of(MODEL.formatted(constructs)), ModulePath.EMPTY);
        compilation.answerEverything();
        return new Compiled(compilation);
    }
}
