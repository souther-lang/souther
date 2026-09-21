package souther.compiler.check;

import java.util.List;
import souther.compiler.core.Core;
import souther.compiler.types.Type;

/**
 * A definition the module emits as a method of its own, as the check settled it.
 *
 * <p>Each parameter is the binder its body reads and the type arriving in it. A parameter the source
 * annotates has the type it wrote; one the lowering added, which no source spells, has the type the
 * check settled the value it carries as. No reader asks the lowered syntax for a type, because a
 * compiler-added parameter has none.
 *
 * @param body the Core the check elaborated for it
 * @param parameters what it takes, in the order a call supplies them
 */
public record EmittedDefinition(Core body, List<Parameter> parameters) {

    /** One parameter: the binding its body reads, and the type arriving in it. */
    public record Parameter(Core.Binder binder, Type type) {}

    public EmittedDefinition {
        parameters = List.copyOf(parameters);
    }
}
