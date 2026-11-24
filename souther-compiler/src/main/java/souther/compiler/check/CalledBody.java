package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.List;
import java.util.Objects;

/**
 * A body beside the bindings a call of it hands values to: the tree an analysis reads, the
 * parameters in the order a call hands them, and what the body binds to the elements of what.
 *
 * <p>The body of a recursive helper is read where a call of it stands, with the parameters
 * standing for what the call handed. The body of a behavior is not: a call of one is a value a
 * run works out, and its body is held this way only to ask which parameters it reads. What the
 * body binds is read in the body's own module, which is where the declarations it names were
 * written.
 *
 * @param body       the body, as the analysis of the behavior reads it
 * @param parameters the bindings a call hands its values to, in the order it hands them
 * @param elements   what the body binds to the elements of what ({@link ElementBindings})
 */
public record CalledBody(Core body, List<Core.Binder> parameters, ElementBindings elements) {

    public CalledBody {
        Objects.requireNonNull(body, "what a call is of has a body");
        parameters = List.copyOf(parameters);
        Objects.requireNonNull(elements, "and binds what it binds, if nothing");
    }
}
