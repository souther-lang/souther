package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

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
    void aQuotientOfTwoNewtypesIsARatioInNeitherOfThem() {
        Diagnostic d = refusalOf("(a: Amount, b: Amount) : Amount", "a / b");
        assertEquals("check.arith.newtype.quotient", d.messageKey(),
                "a quotient leaves the dimension the way a product does, but not for the same reason");
        assertEquals(2, d.secondary().size(), "each operand is named with the newtype it is");
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
    void aScaleIsByTheNewtypesOwnBase() {
        Diagnostic d = refusalOf("(r: Rate, n: Int) : Rate", "r * n");
        assertEquals("check.arith.newtype.scalarbase", d.messageKey());
    }

    @Test
    void anOperandThatIsNotNumericAtAllKeepsTheGenericRefusal() {
        Diagnostic d = refusalOf("(s: String, n: Int) : Int", "s * n");
        assertEquals("check.arith.operand", d.messageKey(),
                "the newtype rules must not absorb the operand rule they were carved out of");
    }
}
