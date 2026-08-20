package souther.compiler.claims;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.List;

/**
 * What an expression evaluates, in the order it evaluates them.
 *
 * <p>One account of evaluation order, for the readers that need one. Which reason an arm aborts
 * with and which fork a body reaches first are two questions about the same order, and each working
 * it out for itself is two chances to disagree about what runs before what.
 *
 * <p>Not {@link Core#forEachChild}, which hands over the slots of a node and is not an account of
 * evaluation. The two differ at a construction: the emitter walks the declared fields and picks
 * each one's initializer out, so what runs first is the field declared first and not the one
 * written first.
 *
 * <p>Strict positions only, and nothing that is not evaluated here. A {@code Block} is a function
 * value: evaluating that position makes the function, and its body runs when a call applies it, on
 * arguments this position does not have.
 */
final class Evaluated {

    /** The strict sub-expressions of {@code e}, in the order they run. */
    static List<Core> inOrder(Core e) {
        if (e instanceof Core.Construct construct) {
            return construct.values().stream().map(Core.FieldValue::value).toList();
        }
        if (e instanceof Core.Block) {
            return List.of();   // made here, run elsewhere
        }
        List<Core> out = new ArrayList<>();
        Core.forEachChild(e, out::add);
        return List.copyOf(out);
    }

    private Evaluated() {}
}
