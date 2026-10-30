package souther.compiler.check;

import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;

/**
 * Where every element of a container stands against a value: no element of
 * {@code List.rangeInclusive(from, to)} is below {@code from}.
 *
 * <p>Kept as the relation and not as a predicate over the element. The bound is a number against
 * an argument of the operation, and a predicate written to say it would be a block no source
 * wrote, read back into the relation it was made from.
 *
 * <p>A form and not the expression it was read from. What an expression stands for is read where
 * it was written, and the element this is taken at is read somewhere else; the form is the value
 * and carries no such place.
 *
 * @param against the value the elements stand against
 * @param offset  added to it
 * @param rel     how an element stands to that
 */
record ElementBound(LinearForm<FactSubject> against, BigDecimal offset, Rel rel)
        implements ElementRelation {}
