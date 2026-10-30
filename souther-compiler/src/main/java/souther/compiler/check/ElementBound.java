package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;

/**
 * Where every element of a container stands against a value: no element of
 * {@code List.rangeInclusive(from, to)} is below {@code from}.
 *
 * <p>Kept as the relation and not as a predicate over the element. The bound is a number against
 * the expression the operation was handed, and a predicate written to say it would be a block no
 * source wrote, read back into the relation it was made from.
 *
 * @param against the value the elements stand against, read where the operation was called
 * @param offset  added to it
 * @param rel     how an element stands to that
 */
record ElementBound(Core against, BigDecimal offset, Rel rel) implements ElementRelation {}
