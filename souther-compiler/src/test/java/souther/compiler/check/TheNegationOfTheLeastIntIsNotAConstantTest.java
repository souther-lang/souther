package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Folding a negation answers what the run time answers. The smallest {@code Int} has no positive
 * counterpart, and negating it aborts at run time, so it is no constant: a fold that wrapped would
 * be a program checked as one number and run as none.
 */
class TheNegationOfTheLeastIntIsNotAConstantTest {

    @Test
    void theLeastIntIsNotNegatedIntoItself() {
        assertEquals(Optional.empty(), ConstantAlgebra.negate(Long.MIN_VALUE));
    }

    @Test
    void everyOtherIntIsNegated() {
        assertEquals(Optional.of(Long.MAX_VALUE), ConstantAlgebra.negate(Long.MIN_VALUE + 1));
        assertEquals(Optional.of(-5L), ConstantAlgebra.negate(5L));
        assertEquals(Optional.of(0L), ConstantAlgebra.negate(0L));
    }
}
