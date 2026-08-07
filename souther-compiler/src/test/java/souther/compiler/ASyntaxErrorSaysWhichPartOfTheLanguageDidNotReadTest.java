package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The five syntax codes, held to what an author was writing when the reading stopped.
 *
 * <p>Every code resolving to a section is checked elsewhere and does not reach this: a parser that
 * answered one code for everything would pass those and still hand a reader the wrong section. What
 * is here is the middle of the chain — the emitter picking the rule its context is about — and it is
 * written against the reader that fails through the shared {@code expect} rather than through a
 * hand-written message, since that is the one that cannot see its own context and has to be told.
 */
class ASyntaxErrorSaysWhichPartOfTheLanguageDidNotReadTest {

    private static String codeOf(String source) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(source));
        return e.code();
    }

    @Test
    void aBehaviorSignatureThatDoesNotReadIsDeclarationSyntax() {
        assertEquals("E2301", codeOf("""
                module demo

                behavior submit : (id Int) -> Int
                """));
    }

    @Test
    void aLambdaMissingItsArrowIsExpressionSyntax() {
        assertEquals("E2302", codeOf("""
                module demo

                data Amount = Int

                let f (xs: List<Int>) : List<Int> = List.map((x) x, xs)
                """));
    }

    @Test
    void aCasePatternThatDoesNotReadIsPatternSyntax() {
        assertEquals("E2303", codeOf("""
                module demo

                data Rank = Manager | Staff
                data Manager
                data Staff

                let name (r: Rank) : Int =
                    match r with
                        | Manager as -> 1
                        | Staff -> 2
                """));
    }

    @Test
    void anExampleRowThatDoesNotReadIsExampleSyntax() {
        assertEquals("E2304", codeOf("""
                module demo

                data Amount = Int

                behavior double : (a: Amount) -> Amount
                    constructs Amount

                let double (a) = Amount(a.value * 2)

                example double
                    | (Amount(1)) Amount(2)
                """));
    }

    @Test
    void aFractionalLiteralWithoutItsSuffixIsLiteralSyntax() {
        assertEquals("E2305", codeOf("""
                module demo

                let rate () : Int = 1.5
                """));
    }

    @Test
    void aCharacterThatBeginsNothingIsNotAboutAnyPartOfTheLanguage() {
        assertEquals("E2306", codeOf("""
                module demo

                let f () : Int = @
                """));
    }
}
