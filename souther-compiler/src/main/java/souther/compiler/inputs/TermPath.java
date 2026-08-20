package souther.compiler.inputs;

import java.util.List;

/**
 * Where in a behavior's input a value sits: a parameter, and the fields read off it.
 *
 * <p>Spelled the way {@code InvariantChecker} spells the same location, because the two will meet. A
 * partition derived from a parameter's type and a threshold read off a {@code guard} are about the
 * same input position or they are not, and if the two spellings disagree the same position becomes
 * two axes — one of which no row ever covers.
 *
 * <p>A newtype's {@code value} is not a step. {@code data Amount = Int} is one location whether it is
 * written {@code request.cost} or {@code request.cost.value}, so the field is never appended and a
 * path always ends at the newtype itself.
 */
public record TermPath(String head, List<String> fields) {

    public TermPath {
        fields = List.copyOf(fields);
    }

    public static TermPath of(String head) {
        return new TermPath(head, List.of());
    }

    public TermPath then(String field) {
        List<String> longer = new java.util.ArrayList<>(fields);
        longer.add(field);
        return new TermPath(head, longer);
    }

    public int depth() {
        return fields.size();
    }

    @Override
    public String toString() {
        return fields.isEmpty() ? head : head + "." + String.join(".", fields);
    }
}
