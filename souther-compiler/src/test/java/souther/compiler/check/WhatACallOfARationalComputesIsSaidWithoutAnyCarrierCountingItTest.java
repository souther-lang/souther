package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.NumericResult;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a call of a {@code Rational} operation computes is said of its arguments, though a
 * {@code Rational} is on no carrier. The statement is held to the declaration all the same: an
 * argument that is no number is refused, so that holding it to a type a carrier does not count
 * stays a question about the arithmetic and not about the carrier.
 */
class WhatACallOfARationalComputesIsSaidWithoutAnyCarrierCountingItTest {

    private static ValueName rational(String name) {
        return ValueName.Stdlib.operation("Rational", name);
    }

    /** Control: each of the six is bound, as the arithmetic it is. */
    @Test
    void theSixOperationsStateWhatTheyCompute() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();

        assertNotNull(facts.answersAFormOfItsArguments(rational("fromInt")));
        assertNotNull(facts.answersAFormOfItsArguments(rational("fromDecimal")));
        assertEquals(BinOp.ADD, facts.operatorComputedBy(rational("add")));
        assertEquals(BinOp.SUB, facts.operatorComputedBy(rational("subtract")));
        assertEquals(BinOp.MUL, facts.operatorComputedBy(rational("multiply")));
        assertEquals(BinOp.DIV, facts.operatorComputedBy(rational("divide")));
    }

    /** What states an arithmetic is no reason to give a Rational a place to count on. */
    @Test
    void aRationalIsStillOnNoCarrier() {
        assertFalse(Carrier.countsToANumber(Type.RATIONAL));
    }

    /** A form over an argument that is no number says nothing a number can be equal to. */
    @Test
    void aFormOverAnArgumentThatIsNoNumberIsRefused() {
        LinearForm<ArgumentRef> form =
                LinearForm.weighing(new ArgumentRef.At(0), ExactRatio.of(1));
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bind(ValueName.Stdlib.operation("String", "length"),
                        new OperationFact.AnswersAFormOfItsArguments(form)));
        assertFalse(e.getMessage().isEmpty());
    }

    /** What an operator computes is no statement about an operation answering a string. */
    @Test
    void arithmeticAnsweredAsAStringIsRefused() {
        assertThrows(IllegalStateException.class,
                () -> bind(ValueName.Stdlib.operation("String", "concat"),
                        new OperationFact.ComputesANumber(
                                new NumericResult<>(
                                        new NumericResult.Answered.Directly(),
                                        new Arithmetic.TheOperator(BinOp.ADD), null))));
    }

    private static void bind(ValueName operation, OperationFact fact) {
        List<OperationFacts.Declared> declared = new ArrayList<>(OperationFacts.declarations());
        declared.add(new OperationFacts.Declared(operation, fact));
        OperationFactBinder.bindAll(DefaultStdlib.get(), declared);
    }
}
