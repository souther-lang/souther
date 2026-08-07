package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The arithmetic rules over a numeric newtype, each paired with the diagnostic it is refused by.
 *
 * <p>Every row of this table is a separate rule, and a refusal that cannot name its own rule sends
 * the author after the wrong fix — the message that says a newtype is not an arithmetic operand
 * reads as an argument for deleting the newtype, which is the opposite of what any of these rules
 * ask for. The generic operand message stays for the one row that is genuinely about a non-numeric
 * operand, so that widening the newtype rules cannot quietly absorb it.
 */
class EveryArithmeticRejectionNamesTheRuleItBrokeTest {

    private static final String TYPES = """
            module demo
            data Amount = Int
            data Quantity = Int
            data Rate = Decimal
            data Inner = Int
            data Outer = Inner
            """;

    private static String source(String signature, String body) {
        return TYPES + "let f " + signature + " = " + body + "\n";
    }

    private static Diagnostic refusalOf(String signature, String body) {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(source(signature, body)),
                signature + " = " + body + " is refused");
        return e.diagnostic();
    }

    private static void allows(String signature, String body) {
        assertDoesNotThrow(() -> Compiler.compile(source(signature, body)),
                signature + " = " + body + " is allowed");
    }

    @Test
    void sameNewtypeAddsAndSubtractsStayingInTheNewtype() {
        allows("(a: Amount, b: Amount) : Amount", "a + b");
        allows("(a: Amount, b: Amount) : Amount", "a - b");
        allows("(a: Amount) : Amount", "a + 100");
    }

    @Test
    void aNewtypeScalesByABareNumberOfItsBase() {
        allows("(a: Amount, n: Int) : Amount", "a * n");
        allows("(n: Int, a: Amount) : Amount", "n * a");
        allows("(a: Amount, n: Int) : Amount", "a / n");
    }

    @Test
    void twoDifferentNewtypesDoNotCombine() {
        Diagnostic d = refusalOf("(a: Amount, q: Quantity) : Amount", "a + q");
        assertEquals("check.arith.newtype.incompatible", d.messageKey());
        assertEquals(2, d.secondary().size(), "each operand is named with the newtype it is");
    }

    @Test
    void aProductOfTwoNewtypesChangesDimension() {
        Diagnostic same = refusalOf("(a: Amount, b: Amount) : Amount", "a * b");
        assertEquals("check.arith.newtype.product", same.messageKey());
        assertEquals(2, same.secondary().size(), "each operand is named with the newtype it is");

        Diagnostic mixed = refusalOf("(a: Amount, q: Quantity) : Amount", "a * q");
        assertEquals("check.arith.newtype.product", mixed.messageKey(),
                "the rule is the same whether or not the two newtypes agree");
    }

    @Test
    void aQuotientOfTwoNewtypesIsAValueInNeitherOfThem() {
        Diagnostic alike = refusalOf("(a: Amount, b: Amount) : Amount", "a / b");
        assertEquals("check.arith.newtype.quotient", alike.messageKey(),
                "a quotient leaves the dimension the way a product does, but not for the same reason");
        assertEquals(2, alike.secondary().size(), "each operand is named with the newtype it is");

        Diagnostic unlike = refusalOf("(a: Amount, q: Quantity) : Amount", "a / q");
        assertEquals("check.arith.newtype.quotient", unlike.messageKey(),
                "unlike newtypes divide into a dimension of their own, which is refused the same way");
    }

    @Test
    void aScalarDividedByANewtypeIsAnInverse() {
        Diagnostic d = refusalOf("(n: Int, a: Amount) : Amount", "n / a");
        assertEquals("check.arith.newtype.reciprocal", d.messageKey());
        assertEquals(2, d.secondary().size(), "each operand is named with the newtype it is");
    }

    @Test
    void aNewtypeOverANewtypeHasNoArithmetic() {
        Diagnostic d = refusalOf("(o: Outer, p: Outer) : Outer", "o + p");
        assertEquals("check.arith.newtype.nested", d.messageKey());
    }

    @Test
    void onlyALiteralIsReadAsTheNewtypeBesideIt() {
        Diagnostic onTheRight = refusalOf("(a: Amount, n: Int) : Amount", "a + n");
        assertEquals("check.arith.newtype.scalar", onTheRight.messageKey());

        Diagnostic onTheLeft = refusalOf("(a: Amount, n: Int) : Amount", "n - a");
        assertEquals("check.arith.newtype.scalar", onTheLeft.messageKey(),
                "which side the bare value stands on does not change the rule it breaks");
    }

    @Test
    void aValueOfAnotherBaseIsRefusedByTheBaseAndNotByTheOperator() {
        Diagnostic scaled = refusalOf("(r: Rate, n: Int) : Rate", "r * n");
        assertEquals("check.arith.newtype.base", scaled.messageKey());

        Diagnostic added = refusalOf("(a: Amount, d: Decimal) : Amount", "a + d");
        assertEquals("check.arith.newtype.base", added.messageKey(),
                "reading its own base is one rule, and `+` is not a scale to be refused as one");
    }

    @Test
    void eitherOperandCanBeTheOneThatIsNotANumber() {
        Diagnostic onTheLeft = refusalOf("(s: String, n: Int) : Int", "s * n");
        assertEquals("check.arith.operand", onTheLeft.messageKey(),
                "the newtype rules must not absorb the operand rule they were carved out of");
        assertEquals(List.of("String"), List.of(onTheLeft.args()));

        Diagnostic onTheRight = refusalOf("(n: Int, s: String) : Int", "n * s");
        assertEquals("check.arith.operand", onTheRight.messageKey(),
                "which side it stands on does not make a String an arithmetic operand");
        assertEquals(List.of("String"), List.of(onTheRight.args()),
                "the operand named is the one that is not a number");
    }

    @Test
    void twoNumbersOfUnlikeBasesAreThePlainMismatchTheyAlwaysWere() {
        Diagnostic d = refusalOf("(n: Int, d: Decimal) : Int", "n * d");
        assertEquals("check.type.mismatch.msg", d.messageKey(),
                "Int beside Decimal is said by a found-versus-expected block, not by a sentence");
    }

    @Test
    void oneNameStandingForTwoTypesIsWrittenOutInTheMessageItself() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compileModules(List.of(
                """
                module one exposing ( Amount )
                data Amount = Int
                """,
                """
                module two exposing ( Amount )
                data Amount = Int
                """,
                """
                module use
                import one ( Amount )
                import two
                let mix (a: Amount, b: two.Amount) : Amount = a + b
                """)));
        assertEquals(List.of("one.Amount", "two.Amount"), List.of(e.diagnostic().args()),
                "`Amount and Amount are different newtypes` names nothing the author can act on");
    }
}
