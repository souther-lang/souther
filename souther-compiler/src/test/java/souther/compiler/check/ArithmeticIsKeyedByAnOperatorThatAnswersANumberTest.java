package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Which operators the two values keyed by one may be keyed by.
 *
 * <p>Both say that an operator is what computes a number: {@link NumericMeaning.Operator} of an
 * expression the check read, and {@link Arithmetic.TheOperator} of an operation the library
 * declared. Every reader of either takes the operator that way — the term a value is named by is
 * built from it, and the recipe a bound is proved in is keyed by it — so one keyed by an operator
 * answering something else would put a comparison where a number is read.
 *
 * <p><b>The set the type admits, not the set anything happens to make.</b> The library states three
 * arithmetic operations and none of them is a divide, and a row for one is writable: the divides it
 * declares today are a truncating quotient and a quotient rounded to a scale, which are arithmetic
 * of their own rather than what the operator computes. So what is refused here is an operator that
 * answers no number, and a divide is not one of those.
 */
class ArithmeticIsKeyedByAnOperatorThatAnswersANumberTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Core number(long value) {
        return new Core.Int(value, Type.INT, POS);
    }

    @Test
    void anExpressionsArithmeticIsKeyedByOneThatAnswersANumber() {
        for (BinOp op : BinOp.values()) {
            if (op.answersANumber()) {
                assertEquals(op, new NumericMeaning.Operator(op, number(1), number(2)).op(),
                        "arithmetic the language writes as an operator is keyed by it: " + op);
            } else {
                assertThrows(IllegalArgumentException.class,
                        () -> new NumericMeaning.Operator(op, number(1), number(2)),
                        "what this is about is arithmetic, and this answers no number: " + op);
            }
        }
    }

    @Test
    void aLibraryOperationComputesWhatAnOperatorAnsweringANumberComputes() {
        for (BinOp op : BinOp.values()) {
            if (op.answersANumber()) {
                assertEquals(op, new Arithmetic.TheOperator(op).op(),
                        "an operation stating this computes what the operator computes: " + op);
            } else {
                assertThrows(IllegalArgumentException.class, () -> new Arithmetic.TheOperator(op),
                        "an operation computing what an operator computes answers a number: " + op);
            }
        }
    }
}
