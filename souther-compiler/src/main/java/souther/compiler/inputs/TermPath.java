package souther.compiler.inputs;

import java.util.List;

/**
 * A parameter-rooted coordinate: a parameter, and the field steps taken from it.
 *
 * <p>It says where, and not what the location belongs to. An input reading writes its positions down
 * this way and so does a plan for building a value, and those are not one set of positions — what a
 * path is about is owned by whatever holds it ({@link Position}, {@code ConstructionPlan.Node}) and
 * is not readable off the coordinate. Read off it, a position of one would be looked up in the
 * other, which is the thing that has to stay impossible.
 *
 * <p>One coordinate for both, and not because they happen to spell alike. A class fixes an input
 * position, and the value that goes there is chosen at a position of the plan; the two meet by being
 * written the same way, so a second type would put a conversion exactly where the meeting is — and
 * the meeting is the protocol. Spelled the way {@code InvariantChecker} spells the same location for
 * that same reason: a partition derived from a parameter's type and a threshold read off a
 * {@code guard} are about one location or they are not, and if the two spellings disagree the same
 * position becomes two axes, one of which no row ever covers.
 *
 * <p>Field steps and nothing else are recorded. That a newtype contributes none of them is not this
 * type's rule and nothing here enforces it — whoever reads a structure takes its steps from the
 * fields {@link StructuralDescent} answers with, off a shape {@code TypeView} has already taken the
 * worn names off. So {@code data Amount = Int} is one location whether it is written
 * {@code request.cost} or {@code request.cost.value}, and a path ends at the newtype itself.
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
