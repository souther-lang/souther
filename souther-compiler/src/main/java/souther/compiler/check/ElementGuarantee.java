package souther.compiler.check;

import souther.compiler.core.Core;

/**
 * What a rule of a container states of every element it holds, kept with the statement of the rule
 * that states it.
 *
 * <p>The rule stays the container's. What this carries to the elements is its consequence — each
 * element satisfies the predicate — and the statement it comes of, so that a reading of the element
 * cites the rule that was written and not a rule of the element's own, and says which of its
 * statements each thing it found is a thing of.
 *
 * <p>The predicate is the block the quantifier was written with, read where it was written. A name
 * in it that is not its parameter stands for something of the container's value, which a reading of
 * one element has no place for.
 *
 * @param statedBy  which statement of which part of which rule of the container states it
 * @param predicate what every element satisfies
 */
public record ElementGuarantee(InvariantStatementId statedBy, Core.Block predicate) {

    public ElementGuarantee {
        if (statedBy == null || predicate == null || predicate.params().size() != 1) {
            throw new IllegalArgumentException(
                    "a guarantee of every element is some statement's predicate of one element");
        }
    }

    /** The part of the rule that states it, which is what a reading is made without. */
    public PartId<RuleRef.Invariant> part() {
        return statedBy.part();
    }
}
