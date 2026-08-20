package souther.compiler.check;

import souther.compiler.check.DischargeRules.Shape;
import souther.compiler.core.Core;

import java.util.Set;

/**
 * A relation known of every element of a container. A fact settles the container as a whole and
 * is keyed by the call that states it, which relates it to nothing inside; this keeps the
 * relation as the clause it was written as, so it can be read again at the element a combinator's
 * closure is handed.
 *
 * <p>{@code through} is how far it travels: a construction of one of those shapes holds only
 * elements of what it was built from, so what was stated of the source still holds of each of
 * them. The predicate is kept as the block it is, already read where the relation was stated, so
 * every name in it means there what it meant there.
 */
record Quantified(FactSubject container, Set<Shape> through, Core.Block predicate) {}
