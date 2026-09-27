package souther.compiler.core;

import java.util.List;

/**
 * How the boundary checks one clause: the constraints parts of it are stated as, in the order they
 * are written, and whether the clause's own condition still has to run after them.
 *
 * <p>Both may hold at once. {@code invariant value.length >= 3 && f(value)}, where only the first
 * part is a constraint, is {@code [MinLength(3)]} and the condition: a value short of three breaks
 * the constraint, and one that is long enough and breaks {@code f} breaks the clause. That is one
 * clause either way, and one clause is what a failure names.
 *
 * <p>A clause no part of which is a constraint is the condition alone, and so is every clause of a
 * data the boundary does not decode as one value — a product, whose clauses are about fields, is
 * checked whole.
 *
 * @param constraints what parts of the clause are stated as, in the order they were written
 * @param checkCondition whether the constraints do not cover the clause, so that its condition has
 *     to hold as well — false only where every part of it is one of the constraints
 */
public record BoundaryCheck(List<BoundaryConstraint> constraints, boolean checkCondition) {

    public BoundaryCheck {
        constraints = List.copyOf(constraints);
        if (constraints.isEmpty() && !checkCondition) {
            throw new IllegalArgumentException(
                    "a clause is checked at the boundary by something: a constraint or itself");
        }
    }

    /** The clause checked as its own condition, nothing of it stated as a constraint. */
    public static BoundaryCheck conditionOnly() {
        return new BoundaryCheck(List.of(), true);
    }
}
