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
 * signature accepted the arguments, so a rule about the operation reads an argument that is there.
 * The one an author wrote can, and does — the totality check runs beside the checks that report an
 * arity rather than after them, so it reads a call already known to be wrong.
 *
 * <p>So {@link Combinators#handedTo(souther.compiler.ast.Ast.Apply)} says nothing about such a call,
 * and the arity is reported by the check whose question it is. Held here because the difference
 * between the two trees is the whole reason one of them is asked and the other is not: were it to
 * stop holding, this fails rather than the walk crediting an element off an argument that is absent.
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

    /** The same where another error is collected first, so nothing is fatal before the walk runs. */
    @Test
    void aCombinatorOfTheWrongArityBesideAnotherError() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compileWithWarnings("""
                module demo
                let go (xs: List<Int>) : List<Int> = List.sortBy(x -> go([x]))
                let other (n: Int) : Int = nosuchthing(n)
                behavior f : (xs: List<Int>) -> List<Int>
                let f (xs) = go(xs)
                """));
        assertTrue(e.getMessage().contains("argument(s)") || e.getMessage().contains("nosuchthing"),
                "one of the two errors, and not an internal failure: " + e.getMessage());
    }
}
