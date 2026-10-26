package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.Map;

/**
 * What an expression is once the names bound on the way to it stand for what they were given.
 *
 * <p>A helper called with arguments is expanded into a binding of each argument round its body, so
 * a rule written through a helper reaches a reader with the helper's parameters as names for what
 * the call handed it. A reader recognising the rule by what it states reads through them.
 */
final class LetBound {

    private LetBound() {}

    /**
     * {@code e} with the bindings it opens recorded in {@code given}, and every name already bound
     * there, and every widening, read through; the first expression that is none of those.
     */
    static Core resolved(Core e, Map<BindingId, Core> given) {
        Core here = Core.withoutStanding(e);
        while (true) {
            if (here instanceof Core.LetIn let) {
                given.put(let.binder().binding(), let.value());
                here = Core.withoutStanding(let.body());
            } else if (here instanceof Core.Widen widened) {
                here = Core.withoutStanding(widened.value());
            } else if (here instanceof Core.Read read && given.containsKey(read.binding())) {
                here = Core.withoutStanding(given.get(read.binding()));
            } else {
                return here;
            }
        }
    }
}
