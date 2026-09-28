package souther.compiler.frontend;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.msg.ParseMessage;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * An integer literal is an {@code Int} when its magnitude is one, and the magnitude of the least
 * {@code Int} is one only under a minus.
 *
 * <p>The minus is a token of its own, so the literal beneath it is read before the negation it
 * belongs to exists, and {@code 9223372036854775808} has no {@code long} to be read into. What is
 * admitted is the whole of {@code -9223372036854775808}; every other negation is still a negation of
 * the literal it was written with.
 */
class TheLeastIntIsWrittenUnderAMinusTest {

    private static Ast.Expr bodyOf(String expression) {
        Ast.Module module = CstFrontend.parse("""
                module m

                behavior least : (a: Int) -> Int
                let least (a) = %s
                """.formatted(expression));
        return module.fns().stream()
                .filter(def -> def.name().equals("least"))
                .findFirst()
                .orElseThrow()
                .writtenBody();
    }

    private static ParseMessage.AnIntegerLiteralIsOutsideInt refusalOf(String expression) {
        CompileException e = assertThrows(CompileException.class, () -> bodyOf(expression));
        assertEquals("E2305", e.diagnostic().code());
        return assertInstanceOf(ParseMessage.AnIntegerLiteralIsOutsideInt.class, e.diagnostic().said());
    }

    @Test
    void theGreatestIntIsAnIntegerLiteral() {
        assertEquals(Long.MAX_VALUE,
                assertInstanceOf(Ast.IntLit.class, bodyOf("9223372036854775807")).value());
    }

    @Test
    void theLeastIntIsWrittenUnderAMinus() {
        assertEquals(Long.MIN_VALUE,
                assertInstanceOf(Ast.IntLit.class, bodyOf("-9223372036854775808")).value());
    }

    @Test
    void bracketsAroundTheMagnitudeDoNotChangeWhatIsAdmitted() {
        assertEquals(Long.MIN_VALUE,
                assertInstanceOf(Ast.IntLit.class, bodyOf("-(9223372036854775808)")).value());
        assertEquals(Long.MIN_VALUE,
                assertInstanceOf(Ast.IntLit.class, bodyOf("-((9223372036854775808))")).value());
    }

    @Test
    void oneMoreThanTheGreatestIsRefusedWhereItIsWrittenBare() {
        assertEquals("9223372036854775808", refusalOf("9223372036854775808").written());
    }

    @Test
    void oneBeyondTheLeastIsRefusedUnderAMinus() {
        assertEquals("9223372036854775809", refusalOf("-9223372036854775809").written());
    }

    @Test
    void aLiteralOfAnyLengthIsRefusedAndNotThrown() {
        refusalOf("99999999999999999999999999999999999999999999");
        refusalOf("-99999999999999999999999999999999999999999999");
    }

    /** Only the one magnitude is read as the least {@code Int}; the minus in front of any other
     * literal is the negation it always was, which the rest of the compiler still reads as one. */
    @Test
    void aNegationOfAnyOtherLiteralStaysANegation() {
        Ast.Neg neg = assertInstanceOf(Ast.Neg.class, bodyOf("-9223372036854775807"));
        assertEquals(Long.MAX_VALUE, assertInstanceOf(Ast.IntLit.class, neg.operand()).value());
        assertInstanceOf(Ast.Neg.class, bodyOf("-5"));
    }

    @Test
    void aRowMayStateTheLeastInt() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module m

                behavior least : (a: Int) -> Int
                let least (a) = a

                example least
                    | "the smallest Int" : (-9223372036854775808) -> -9223372036854775808
                """));
    }
}
