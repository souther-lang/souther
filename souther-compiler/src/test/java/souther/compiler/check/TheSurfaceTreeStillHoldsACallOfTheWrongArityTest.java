package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which of the two trees can hold a call the operation's signature would not accept.
 *
 * <p>The one a representation keeps standing cannot: a {@code PreservedCall} is built only where the
 * signature accepted the arguments and typed the block it was handed, so a rule about the operation
 * reads an argument that is there and a parameter the block has. The one an author wrote can, and
 * does — the totality check runs beside the checks that report an arity rather than after them, so it
 * reads a call already known to be wrong.
 *
 * <p>Two ways for one to be wrong, and both arrive. A call written with fewer arguments than the
 * operation takes, and a block written with fewer parameters than the operation applies one to. A
 * sugar is how each gets this far: it has no declaration of its own, so what is said about the arity
 * of {@code List.fold} is said against the call it becomes, and by then the walk has read it.
 *
 * <p>So {@link Combinators#handedTo(souther.compiler.ast.Ast.Apply)} says nothing about such a call,
 * and the arity is reported by the check whose question it is. Held here because the difference
 * between the two trees is the whole reason one of them is asked and the other is not: were it to
 * stop holding, this fails rather than the walk crediting an element off something that is absent.
 */
class TheSurfaceTreeStillHoldsACallOfTheWrongArityTest {

    private static void arityIsWhatIsReported(String written, String src) {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileWithWarnings(src));
        assertTrue(e.getMessage().contains("argument(s)"),
                written + " should be reported as the arity it is, and was: " + e.getMessage());
    }

    /** A combinator inside a recursive helper — the one body the totality check walks. */
    @Test
    void aCombinatorWrittenWithoutItsContainer() {
        arityIsWhatIsReported("List.sortBy", """
                module demo
                let go (xs: List<Int>) : List<Int> = List.sortBy(x -> go([x]))
                behavior f : (xs: List<Int>) -> List<Int>
                let f (xs) = go(xs)
                """);
    }

    /**
     * And a sugar, which the totality check reads under the name the author wrote. A sugar is the
     * call it becomes with some arguments already supplied, so one written with too few is not that
     * call and is reported as no operation at all — a different question with a different answer, and
     * either way not this walk's.
     */
    @Test
    void aSugarWrittenWithoutItsContainer() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compileWithWarnings("""
                module demo
                let go (xs: List<Int>) : Int = List.fold((acc, x) -> acc + go([x]), 0)
                behavior f : (xs: List<Int>) -> Int
                let f (xs) = go(xs)
                """));
        assertTrue(e.getMessage().contains("List.fold"),
                "the call should be reported as what is wrong with it: " + e.getMessage());
    }

    /**
     * A block written with fewer parameters than the operation applies one to. The element arrives on
     * a parameter the block does not have, which is nothing to say rather than something to read off
     * the parameter list at that position.
     */
    @Test
    void aStepWrittenWithoutTheParameterItsElementArrivesOn() {
        parameterCountIsWhatIsReported("""
                module demo
                let go (xs: List<Int>) : Int = List.fold(acc -> go(xs), 0, xs)
                behavior f : (xs: List<Int>) -> Int
                let f (xs) = go(xs)
                """);
        parameterCountIsWhatIsReported("""
                module demo
                let go (s: Set<Int>) : Int = Set.fold(acc -> go(s), 0, s)
                behavior f : (s: Set<Int>) -> Int
                let f (s) = go(s)
                """);
    }

    private static void parameterCountIsWhatIsReported(String src) {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileWithWarnings(src));
        // Which check reports it depends on whether the sugar's target is expanded or applied, and
        // the two word it differently. That either says it is the point; an internal failure would
        // not be a CompileException at all.
        assertTrue(e.getMessage().contains("parameter(s)") || e.getMessage().contains("argument(s)"),
                "the block should be reported for what it is written with, and was: "
                        + e.getMessage());
    }

    /** The same where another error is collected first, so nothing is fatal before the walk runs. */
    @Test
    void aCombinatorOfTheWrongArityBesideAnotherError() {
        besideAnotherError("""
                module demo
                let go (xs: List<Int>) : List<Int> = List.sortBy(x -> go([x]))
                let other (n: Int) : Int = nosuchthing(n)
                behavior f : (xs: List<Int>) -> List<Int>
                let f (xs) = go(xs)
                """);
        besideAnotherError("""
                module demo
                let go (xs: List<Int>) : Int = List.fold(acc -> go(xs), 0, xs)
                let other (n: Int) : Int = nosuchthing(n)
                behavior f : (xs: List<Int>) -> Int
                let f (xs) = go(xs)
                """);
    }

    private static void besideAnotherError(String src) {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileWithWarnings(src));
        assertTrue(e.getMessage().contains("argument(s)") || e.getMessage().contains("nosuchthing")
                        || e.getMessage().contains("List.fold"),
                "one of the two errors, and not an internal failure: " + e.getMessage());
    }
}
