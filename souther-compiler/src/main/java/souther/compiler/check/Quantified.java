package souther.compiler.check;

import souther.compiler.semantics.ElementShape;
import souther.compiler.core.Core;

import java.util.Optional;
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
 * <p>{@code origin} is the statement of a declaration's rule that states it, where it was read off a
 * declaration's rules. A relation read off a guard or a body, or an operation's guarantee, is no
 * statement of a rule and has none. What a reading of an element takes from a rule is attributed to
 * that statement, which is the one place its identity is issued: numbered where each element is
 * read, one statement would be as many as there are places.
 */
record Quantified(FactSubject container, Set<ElementShape> through, Core.Block predicate,
                  Optional<InvariantStatementId> origin) implements ElementRelation {

    Quantified(FactSubject container, Set<ElementShape> through, Core.Block predicate) {
        this(container, through, predicate, Optional.empty());
    }

    /** The same relation, stated by {@code statement} of a rule. */
    Quantified statedBy(InvariantStatementId statement) {
        return new Quantified(container, through, predicate, Optional.of(statement));
    }

    /** What a rule of the container states of each element, where this is one. */
    Optional<ElementGuarantee> asGuarantee() {
        return origin.map(statement -> new ElementGuarantee(statement, predicate));
    }
}
