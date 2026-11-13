package souther.compiler.check;

import souther.compiler.core.Core;

/**
 * What a rule of a container states of every element it holds, kept with the part of the rule that
 * states it.
 *
 * <p>The rule stays the container's. What this carries to the elements is its consequence — each
 * element satisfies the predicate — and the part it comes of, so that a reading of the element
 * cites the rule that was written and not a rule of the element's own.
 *
 * <p>The predicate is the block the quantifier was written with, read where it was written. A name
 * in it that is not its parameter stands for something of the container's value, which a reading of
 * one element has no place for.
 *
 * @param part      which part of which rule of the container states it
 * @param predicate what every element satisfies
 */
public record ElementGuarantee(PartId<RuleRef.Invariant> part, Core.Block predicate) {

    public ElementGuarantee {
        if (part == null || predicate == null || predicate.params().size() != 1) {
            throw new IllegalArgumentException(
                    "a guarantee of every element is some part's predicate of one element");
        }
    }
}
