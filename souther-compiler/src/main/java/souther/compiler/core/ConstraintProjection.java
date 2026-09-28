package souther.compiler.core;

import java.util.List;

/**
 * What a clause is as standard constraints on the one field of the data it governs: the constraints
 * parts of it are exactly, in the order they are written, and whether those constraints are the
 * whole of the clause.
 *
 * <p>A fact about the clause and the field, and not an instruction about where it is checked. A
 * newtype and a product of one field hold the same clauses of the same field, and each clause is
 * the same constraints of it whichever form was written. Whether the constraints are what a value
 * is checked by is decided by how the value crosses: a newtype's decoder checks them, and runs the
 * condition as well where they are not the whole clause; a product crosses as an object and runs
 * each clause as the rule it is.
 *
 * <p>{@code invariant value.length >= 3 && f(value)}, where only the first part is a constraint, is
 * {@code [MinLength(3)]} and not complete. {@code invariant value.length >= 3} is the same
 * constraint and complete. A clause none of whose parts is a constraint, and every clause of a data
 * of more than one field — which has no one field for a constraint to be about — is
 * {@link #none()}.
 *
 * @param constraints what parts of the clause are, in the order they were written
 * @param complete whether the constraints say everything the clause says, so that a value meeting
 *     them meets the clause
 */
public record ConstraintProjection(List<BoundaryConstraint> constraints, boolean complete) {

    public ConstraintProjection {
        constraints = List.copyOf(constraints);
        if (constraints.isEmpty() && complete) {
            throw new IllegalArgumentException(
                    "a clause is not the whole of no constraint: it says something");
        }
    }

    /** A clause nothing of which is a constraint. */
    public static ConstraintProjection none() {
        return new ConstraintProjection(List.of(), false);
    }
}
