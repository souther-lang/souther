package souther.compiler.check;

import souther.compiler.semantics.ElementShape;
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
 *
 * <p>{@code origin} is the part of a declaration's rule that states it, where it was read off a
 * declaration's rules, and null where it was read off a guard or a body. What a reading of an
 * element takes from it is attributed to that part.
 */
record Quantified(FactSubject container, Set<ElementShape> through, Core.Block predicate,
                  PartId<RuleRef.Invariant> origin) implements ElementRelation {

    Quantified(FactSubject container, Set<ElementShape> through, Core.Block predicate) {
        this(container, through, predicate, null);
    }

    /** The same relation, stated by {@code part} of a rule. */
    Quantified statedBy(PartId<RuleRef.Invariant> part) {
        return new Quantified(container, through, predicate, part);
    }
}
