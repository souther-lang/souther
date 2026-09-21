package souther.compiler.check;

import java.util.List;
import souther.compiler.core.Core;
import souther.compiler.types.Type;

/**
 * A definition the module emits as a method of its own, as the check settled it.
 *
 * <p>What it takes is a type per parameter, in the order the lowered definition lists them. A
 * parameter the source annotates has the type it wrote; one the lowering added, which no source
 * spells, has the type the check settled the value it carries as. No reader asks a parameter for a
 * type annotation, because a compiler-added parameter has none.
 *
 * @param body the Core the check elaborated for it
 * @param parameterTypes the type of each parameter
 */
public record EmittedDefinition(Core body, List<Type> parameterTypes) {

    public EmittedDefinition {
        parameterTypes = List.copyOf(parameterTypes);
    }
}
