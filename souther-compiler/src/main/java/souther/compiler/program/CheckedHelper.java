package souther.compiler.program;

import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * A helper the module emits as a definition of its own.
 *
 * <p>Most helpers are gone by the time a module is checked: the checker inlines a {@code let} at
 * the place it is used. What is left here is the one that cannot be inlined — a recursion — and a
 * body reaches it by a call like any other. A reader given only the behaviors would find that call
 * naming something it had never been handed.
 *
 * <p>What it answers is not a member: it is {@code body().type()}, which the checker decided.
 */
public final class CheckedHelper {

    private final ValueName.Helper name;
    private final List<Parameter> parameters;
    private final Core body;

    CheckedHelper(ValueName.Helper name, List<Parameter> parameters, Core body) {
        this.name = name;
        this.parameters = List.copyOf(parameters);
        this.body = body;
    }

    /** One parameter: the binding its body reads, and the type arriving in it. */
    public record Parameter(Core.Binder binder, Type type) {}

    /** The name a call in a body reaches this helper by. */
    public ValueName.Helper name() {
        return name;
    }

    /** Its parameters, in the order a call supplies them. */
    public List<Parameter> parameters() {
        return parameters;
    }

    /** Its body, as the checker typed it. */
    public Core body() {
        return body;
    }

    @Override
    public String toString() {
        return name.module() + "." + name.name();
    }
}
