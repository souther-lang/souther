package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.WhereItSits;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.PhysicalPos;
import souther.compiler.diag.Primary;
import souther.compiler.diag.msg.ArithmeticMessage;
import souther.compiler.diag.msg.HelperMessage;
import souther.compiler.diag.msg.Message;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a library operation is handed in place of a function is checked at the call, against what
 * the body has bound where the call is written, and the report names the operation as the call
 * spells it.
 *
 * <p>The check runs on the body before the library's own body is expanded into it, so it is the one
 * place a mistake can be reported in the author's terms. Past it, the same mistake is found inside
 * the expansion: at the whole call, about the library's own parameter, in a body this compile has no
 * source for. So a binding the check does not see is a binding whose mistakes are reported there,
 * and the rows below are the places a binding comes into force — a parameter, a {@code let}, a
 * {@code let} of a {@code let}, and a block's own parameter.
 *
 * <p>The scope is keyed by the binding and not by its spelling, which only a row with two bindings of
 * one name can tell apart: the inner one is what the call reads, and the outer one is a type the
 * call must not be held to.
 */
class AFunctionArgumentIsCheckedInTheScopeItIsWrittenInTest {

    /** What every call below is written as. */
    private static final String WROTE = "List.map";

    @Test
    void aParameterHandedOverIsReportedAtTheParameter() {
        String source = """
                module m

                behavior f : (xs: List<Int>, k: Int) -> List<Int>
                let f (xs, k) = List.map(k, xs)
                """;

        HelperMessage.AValueWhereAFunctionIsTaken said = aValueWhereAFunctionIsTaken(source, "k");
        assertEquals(WROTE, said.call());
        assertEquals("k", said.written());
    }

    @Test
    void aLetOfAValueHandedOverIsReportedAtTheName() {
        String source = """
                module m

                behavior f : (xs: List<Int>, k: Int) -> List<Int>
                let f (xs, k) = {
                    let j = k
                    List.map(j, xs)
                }
                """;

        HelperMessage.AValueWhereAFunctionIsTaken said = aValueWhereAFunctionIsTaken(source, "j");
        assertEquals(WROTE, said.call());
        assertEquals("j", said.written());
    }

    @Test
    void soIsALetOfThatLet() {
        String source = """
                module m

                behavior f : (xs: List<Int>, k: Int) -> List<Int>
                let f (xs, k) = {
                    let j = k
                    let q = j
                    List.map(q, xs)
                }
                """;

        assertEquals("q", aValueWhereAFunctionIsTaken(source, "q").written());
    }

    /** The block's own parameter is an {@code Int} because the outer call hands it the elements of
     *  a {@code List<Int>}, and nothing but that call says so. */
    @Test
    void aBlocksParameterHandedOverIsReportedAtTheParameter() {
        String source = """
                module m

                behavior f : (xs: List<Int>, ys: List<Int>) -> List<List<Int>>
                let f (xs, ys) = List.map(x -> List.map(x, ys), xs)
                """;

        assertEquals("x", aValueWhereAFunctionIsTaken(source, "x,").written());
    }

    /** The inner {@code j} holds a function and the outer one an {@code Int}. A scope that found the
     *  name by its spelling would hold the call to the outer one and refuse it. */
    @Test
    void aLetOfAFunctionIsNotReadAsTheValueItShadows() {
        String source = """
                module m

                let f (xs: List<Int>, j: Int, g: (Int) -> Int): List<Int> = {
                    let j = g
                    List.map(j, xs)
                }

                behavior go : (xs: List<Int>) -> List<Int>
                let go (xs) = f(xs, 1, x -> x + 1)
                """;

        assertDoesNotThrow(() -> Compiler.compile(source));
    }

    /** A value that does not type is the elaboration's to report, as it is with no call after it. */
    @Test
    void aLetWhoseValueDoesNotTypeIsReportedAsThatAndNotAsTheCall() {
        String source = """
                module m

                behavior f : (xs: List<Int>, k: Int) -> List<Int>
                let f (xs, k) = {
                    let j = k + "one"
                    List.map(j, xs)
                }
                """;

        assertInstanceOf(ArithmeticMessage.AnOperandIsNotANumber.class,
                refused(source).diagnostic().said());
    }

    @Test
    void aBlockOfAnotherArityNamesTheOperationAsWritten() {
        String source = """
                module m

                behavior f : (xs: List<Int>) -> List<Int>
                let f (xs) = List.map((a, b) -> a, xs)
                """;

        Message said = refused(source).diagnostic().said();
        assertEquals(WROTE,
                assertInstanceOf(HelperMessage.TheBlockTakesAnotherNumberOfArguments.class, said)
                        .call());
    }

    @Test
    void aBlockAnsweringAnotherTypeNamesTheOperationAsWritten() {
        String source = """
                module m

                behavior f : (xs: List<Int>) -> List<Int>
                let f (xs) = List.filterMap(x -> x + 1, xs)
                """;

        Message said = refused(source).diagnostic().said();
        assertEquals("List.filterMap",
                assertInstanceOf(HelperMessage.TheBlockAnswersAnotherType.class, said).call());
    }

    @Test
    void aCallOfAnotherArityNamesTheOperationAsWritten() {
        String source = """
                module m

                behavior f : (xs: List<Int>) -> List<Int>
                let f (xs) = List.map(xs)
                """;

        Message said = refused(source).diagnostic().said();
        assertEquals(WROTE,
                assertInstanceOf(HelperMessage.CalledWithAnotherNumberOfArguments.class, said)
                        .call());
    }

    /** The report, held to be the one about a value handed to a function parameter and to start
     *  where {@code at} is first written in the call's line. */
    private static HelperMessage.AValueWhereAFunctionIsTaken aValueWhereAFunctionIsTaken(
            String source, String at) {
        CompileException e = refused(source);
        HelperMessage.AValueWhereAFunctionIsTaken said = assertInstanceOf(
                HelperMessage.AValueWhereAFunctionIsTaken.class, e.diagnostic().said(),
                () -> "refused as something else: " + e.getMessage());
        PhysicalPos start = WhereItSits.in(source,
                ((Primary.InSource) e.diagnostic().primary()).place().region()).start();
        String[] lines = source.split("\n", -1);
        int line = lastLineCalling(lines);
        assertEquals(line + 1, start.line(), () -> "reported on another line: " + e.getMessage());
        assertEquals(lines[line].indexOf(at, lines[line].indexOf(WROTE)) + 1, start.column(),
                () -> "reported at another column: " + e.getMessage());
        return said;
    }

    /** The line the innermost call is written on. */
    private static int lastLineCalling(String[] lines) {
        for (int i = lines.length - 1; i >= 0; i--) {
            if (lines[i].contains(WROTE)) {
                return i;
            }
        }
        throw new IllegalArgumentException("no line calls " + WROTE);
    }

    private static CompileException refused(String source) {
        return assertThrows(CompileException.class, () -> Compiler.compile(source));
    }
}
