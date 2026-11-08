package souther.compiler.inputs;

import souther.compiler.types.ValueName;

import java.util.Objects;

/**
 * A number an operation accumulates over what is made of each element of a container, said as a
 * rule wrote it: the operation, where the elements stand, what each adds.
 *
 * <p>Not a term. Which term it is — a taking of the container, or a run over a place of its
 * elements or over what is computed of each — is settled where a body's total is settled
 * ({@link InputNumber#totalOf}), so a rule and a body that add up the same numbers are one term
 * by how it was made and never by two readers agreeing on a shape.
 *
 * @param elements where the elements stand, {@code lines[*]}
 * @param each     what each element adds
 */
record TotalOfTheElements(ValueName.Stdlib operation, TermPath elements, ElementValue each) {

    TotalOfTheElements {
        Objects.requireNonNull(operation, "a total is taken by some operation");
        Objects.requireNonNull(elements, "over the elements of some container");
        Objects.requireNonNull(each, "of something made of each");
    }
}
