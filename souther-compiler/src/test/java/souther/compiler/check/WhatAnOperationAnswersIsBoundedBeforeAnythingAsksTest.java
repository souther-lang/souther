package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * That a size is never negative and that {@code Int.abs(x)} is not are one proposition about two
 * operations, and it was written twice in two vocabularies over two halves of the operations it is
 * true of (#1016): the declarations had the second, and a partition reading a guard had the first
 * written into the kind of term it was reading. Each half was reachable from one reader.
 *
 * <p>So the test of the ownership is that neither depends on who is asking. Asked of the operation,
 * with no call and no term in hand, both answer — which is what a reader arriving later gets for
 * nothing, and what the older arrangement could not have given it.
 */
class WhatAnOperationAnswersIsBoundedBeforeAnythingAsksTest {

    private static NumericDomain.Bounds asked(String module, String operation,
                                              ConstantArguments arguments) {
        return ResultRange.of(ValueName.Stdlib.operation(module, operation), arguments);
    }

    private static NumericDomain.Bounds atLeast(long count) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(count)), null);
    }

    /** The half that was declared, asked with nothing standing at the call. */
    @Test
    void anAbsoluteValueIsNotNegativeWithNothingToAsk() {
        assertEquals(atLeast(0), asked("Int", "abs", ConstantArguments.NONE));
        assertEquals(atLeast(0), asked("Decimal", "abs", ConstantArguments.NONE));
    }

    /** The half that was written into the term, asked the same way. Four operations and one
     *  declaration each, none of them written beside the others. */
    @Test
    void everyMeasureAnswersACountThatIsNotNegative() {
        for (ValueName measure : NumericMeasures.calls()) {
            assertEquals(atLeast(0), ResultRange.of(measure, ConstantArguments.NONE),
                    measure + " counts what it is given, and there is no negative number of them");
        }
    }

    /**
     * And what the projection onto a range cannot carry, which is the reason it is not the only
     * reader of these. {@code Int.floorMod(x, k)} is below {@code k} and at or above nought where
     * {@code k} reads as a constant above zero — so a reader that cannot say what {@code k} is gets
     * neither end, and the same rows read against a call that can get both.
     */
    @Test
    void aBoundAgainstAnArgumentIsThereWhenTheArgumentIs() {
        assertEquals(NumericDomain.Bounds.OPEN,
                asked("Int", "floorMod", ConstantArguments.NONE),
                "nothing is known of the divisor, so neither end of the remainder is");
        ConstantArguments hundred = argument ->
                argument.equals(new ArgumentRef.At(1)) ? Optional.of(BigDecimal.valueOf(100))
                        : Optional.empty();
        assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)),
                        Endpoint.exclusive(Count.of(100))),
                asked("Int", "floorMod", hundred));
    }
}
