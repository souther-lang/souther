package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultBound;
import souther.compiler.semantics.ResultRange;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

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
     *
     * <p>What is dropped here is the whole row and not one end of it: the condition on the arguments
     * is what fails, before anything is asked about where the end stands.
     */
    @Test
    void aBoundAgainstAnArgumentIsThereWhenTheArgumentIs() {
        assertEquals(NumericDomain.Bounds.OPEN,
                asked("Int", "floorMod", ConstantArguments.NONE),
                "nothing is known of the divisor, so neither end of the remainder is");
        assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)),
                        Endpoint.exclusive(Count.of(100))),
                asked("Int", "floorMod", constantAt(1, 100)));
    }

    /**
     * The other way a row is dropped, and the one the conditional rows above cannot show: the row
     * holds wherever the operation is called, and it is the argument it stands against that this
     * reader cannot name. {@code Decimal.toInt} is within one of what it rounds under no condition
     * at all, so what decides here is only whether the number it is within one of can be answered
     * for.
     *
     * <p>Both ends of it are strict, which is the other thing this pins: a row read onto a range
     * keeps whether its end is one of the values.
     */
    @Test
    void aBoundHoldingAlwaysIsStillDroppedWhereItsArgumentCannotBeNamed() {
        assertEquals(NumericDomain.Bounds.OPEN,
                asked("Decimal", "toInt", ConstantArguments.NONE),
                "what it rounds is not known here, so neither end of what it rounds to is");
        assertEquals(new NumericDomain.Bounds(Endpoint.exclusive(Count.of(2)),
                        Endpoint.exclusive(Count.of(4))),
                asked("Decimal", "toInt", constantAt(1, 3)),
                "rounding a three lands within one of it, and reaches neither end");
    }

    /** A reader that knows one argument's value and nothing else. */
    private static ConstantArguments constantAt(int position, long value) {
        return argument -> argument.equals(new ArgumentRef.At(position))
                ? Optional.of(BigDecimal.valueOf(value)) : Optional.empty();
    }

    /**
     * And what a bound may not be at all. Every relation but one names an end; a result that is
     * anything other than one value names two ranges with a hole between them, which is not a bound
     * and is refused where a bound is made rather than by whoever reads one.
     */
    @Test
    void aBoundCannotBeWrittenAsADisequality() {
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new ResultBound(null, BigDecimal.ZERO, Rel.NE,
                        new ResultBound.Provided.Always()));
        assertTrue(refused.getMessage().contains("NE"), refused.getMessage());
    }
}
