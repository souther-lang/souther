package souther.compiler.inputs;

import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.Rel;

import java.util.List;

/**
 * What a run has to meet to get past one construction it works out on the way to a rule: the
 * numbers the construction is made of lie where the clauses of the type made leave them.
 *
 * <p>A condition on the run and not a row that stops: a construction asks it of every run that
 * works it out, and a run that does not meet it ends there. Which rows meet it is the way to the
 * rule's to say, and where the declarations already hold it, nothing is asked of a run here and no
 * construction is said.
 *
 * <p>Said of the construction as the model wrote it, so two constructions that ask the same are
 * two of these, as they are two places a run may end.
 *
 * <p>The same condition is what narrows the rows the rule is read over; this is that condition
 * told, and nothing here is worked out again from the text.
 *
 * @param construction the type made, as it is written
 * @param at           where the construction is written
 * @param asks         what it asks
 */
public record WhatAConstructionAsks(String construction, SourcePos at, Asked asks) {

    public WhatAConstructionAsks {
        if (construction == null || at == null || asks == null) {
            throw new IllegalArgumentException("a construction of some type asks something");
        }
    }

    /** What is asked of the numbers of the input. */
    public sealed interface Asked permits Is, AllOf, OneOf {}

    /**
     * One form of the numbers of the input stands {@code rel} to a number.
     *
     * @param form    the numbers weighed and a constant, as an author would write them
     * @param rel     how it stands to {@code against}
     * @param against the number, written as a decimal
     */
    public record Is(String form, Rel rel, String against) implements Asked {

        public Is {
            if (form == null || rel == null || against == null) {
                throw new IllegalArgumentException("a form stands some way to some number");
            }
        }
    }

    /** Every one of these is asked. */
    public record AllOf(List<Asked> each) implements Asked {

        public AllOf {
            each = List.copyOf(each);
            if (each.size() < 2) {
                throw new IllegalArgumentException("two things asked together, or one asked alone");
            }
        }
    }

    /** At least one of these is asked to hold. */
    public record OneOf(List<Asked> each) implements Asked {

        public OneOf {
            each = List.copyOf(each);
            if (each.size() < 2) {
                throw new IllegalArgumentException("two things one of which holds, or one alone");
            }
        }
    }
}
