package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Severity;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.ArmObservation;

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
 * refused one checks exactly as it would have — and the class it is emitted as constructs the one
 * that was not emitted. So the answer is a closure, and what it is closed over is what an
 * implementation references.
 *
 * <p><b>Which is wider than a body, and wider than a module.</b> A {@code >->} composition is an
 * implementation with no body of its own, and it applies its stages by constructing them. A body's
 * call and a stage both reach the declaring module's implementation, whichever module that is. Each
 * of those is a way for the closure to be cut short, so each has a case here.
 */
class WhatMayBeRunIsClosedUnderWhatAnImplementationReferencesTest {

    /**
     * A chain of callers over a body the invariant refuses, a composition over the chain, and one
     * behavior off to the side.
     *
     * <p>{@code %s} is what {@code mint} constructs, so the two readings below differ in that and in
     * nothing else.
     *
     * <p><b>The chain is declared against the direction it is read in.</b> Each caller stands before
     * what it calls, so the first walk of the implementations meets {@code thrice} while
     * {@code twice} is still standing. Declared the other way round, one walk would take the whole
     * chain away and a reading that stopped after one would pass.
     */
    private static final String MODEL = """
            module example.chain

            data Seat = Int
                invariant value >= 1 && value <= 300

            behavior apart : (n: Int) -> Int
            let apart (n) = n

            behavior onwards = apart >-> thrice

            behavior thrice : (n: Int) -> Seat
            let thrice (n) = twice(n)

            behavior twice : (n: Int) -> Seat
            let twice (n) = mint(n)

            behavior mint : (n: Int) -> Seat
                constructs Seat
            let mint (n) = Seat(%s)
            """;

    /** The module a caller imports from, whose own chain ends at the refused body. */
    private static final String DOWN = """
            module example.down exposing ( Seat, twice )

            data Seat = Int
                invariant value >= 1 && value <= 300

            behavior twice : (n: Int) -> Seat
            let twice (n) = mint(n)

            behavior mint : (n: Int) -> Seat
                constructs Seat
            let mint (n) = Seat(%s)
            """;

    /** And the caller, whose own body checks and whose call crosses into the module above. */
    private static final String UP = """
            module example.up

            import example.down ( Seat, twice )

            behavior use : (n: Int) -> Seat
            let use (n) = twice(n)
            """;

    /** What this compiler refuses a construction its own invariant rejects. */
    private static final String THE_REFUSED_CONSTRUCTION = "E2010";

    /**
     * Where every implementation came out, every one of them may be run.
     *
     * <p>Here so that each reading below is a difference and not a coincidence. Answered with one
     * name whatever the model, every case would pass with the closure removed.
     */
    @Test
    void whereEveryImplementationCameOutEveryOneOfThemMayBeRun() {
        Compiled clean = compile("1", MODEL);

        assertEquals(List.of(), clean.refusals(),
                () -> "nothing is refused about this model, and it was refused about "
                        + clean.refusals());
        assertEquals(Set.of("apart", "thrice", "twice", "mint", "onwards"),
                clean.runnable("example.chain"));
    }

    /**
     * A refused body takes every implementation that reaches it, the composition included.
     *
     * <p>The chain is what says this is a closure: {@code thrice} calls {@code twice} and
     * {@code twice} calls the refused body, so an answer that took away only what reaches a refused
     * body directly would keep {@code thrice}. The composition is what says the closure is over
     * implementations and not over bodies — it has none, and it applies {@code thrice} by
     * constructing it.
     */
    @Test
    void aRefusedBodyTakesEveryImplementationThatReachesIt() {
        Compiled refused = compile("0", MODEL);

        assertEquals(List.of(THE_REFUSED_CONSTRUCTION), refused.refusals(),
                () -> "this model is refused about the construction alone, and it was refused"
                        + " about " + refused.refusals());
        assertEquals(Set.of("apart"), refused.runnable("example.chain"));
    }

    /**
     * And it takes a caller in another module with it.
     *
     * <p>A body's call reaches the declaring module's implementation whichever module that is, so a
     * caller here is emitted as a class constructing one that module did not emit. Cut at the module
     * boundary, this answer would vouch for it.
     */
    @Test
    void aRefusedBodyTakesACallerInAnotherModuleWithIt() {
        Compiled refused = compile("0", DOWN, UP);

        assertEquals(List.of(THE_REFUSED_CONSTRUCTION), refused.refusals(),
                () -> "this model is refused about the construction alone, and it was refused"
                        + " about " + refused.refusals());
        assertEquals(Set.of(), refused.runnable("example.down"));
        assertEquals(Set.of(), refused.runnable("example.up"));
    }

    /**
     * And what an evaluation of that caller's module is entitled to emit is nothing.
     *
     * <p>The answer above is what may be run; this is the elaboration an evaluation reads and the
     * classes it loads. They come apart wherever the elaboration is chosen by a narrower question
     * than the closure — the caller's own module comes out whole, so a shortcut taken on that alone
     * hands an evaluation the shipped program and its class constructing one nothing emitted.
     */
    @Test
    void andAnEvaluationOfThatCallersModuleIsEntitledToEmitNothing() {
        Compiled refused = compile("0", DOWN, UP);

        Answer<Bodies.Elaborated> observed =
                refused.compilation().db().ask(new Bodies.Observable("example.up"));
        assertTrue(observed.present(), "the module's names came out, so there is an answer here");
        assertEquals(Set.of(), observed.value().emits(),
                "nothing of this module may be run, so it is entitled to no implementation");

        Set<String> classes = refused.compilation().db()
                .ask(new Output.Evaluated("example.up", ArmObservation.RECORD))
                .value().classes().keySet();
        assertFalse(classes.contains(SoutherJvmAbi.nameOf(
                        new GeneratedClass.BehaviorImpl("example.up", "use")).binaryName()),
                () -> "`use` reaches an implementation nothing made and something implements it: "
                        + classes);
    }

    /** And where the module it imports from came out, the caller may be run. */
    @Test
    void whereTheModuleItImportsFromCameOutTheCallerMayBeRun() {
        Compiled clean = compile("1", DOWN, UP);

        assertEquals(List.of(), clean.refusals(),
                () -> "nothing is refused about this model, and it was refused about "
                        + clean.refusals());
        assertEquals(Set.of("twice", "mint"), clean.runnable("example.down"));
        assertEquals(Set.of("use"), clean.runnable("example.up"));
    }

    /** A compilation of the model, and the answers this asks of it. */
    private record Compiled(Compilation compilation) {

        Set<String> runnable(String module) {
            Answer<Bodies.Implementations> answer =
                    compilation.db().ask(new Bodies.RunnableImplementations(module));
            assertTrue(answer.present(), "a module that settled is one this answers about");
            return answer.value().runnable();
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

    private static Compiled compile(String constructs, String... sources) {
        List<String> texts = new java.util.ArrayList<>();
        for (String source : sources) {
            texts.add(source.contains("%s") ? source.formatted(constructs) : source);
        }
        Compilation compilation = Compilation.ofSources(texts, ModulePath.EMPTY);
        compilation.answerEverything();
        return new Compiled(compilation);
    }
}
