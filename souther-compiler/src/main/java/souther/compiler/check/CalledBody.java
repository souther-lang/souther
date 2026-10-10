package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.List;
import java.util.Objects;

/**
 * The body of a behavior as a call of it is read: the tree an analysis reads, the parameters a call
 * hands values to in the order it hands them, and what the body binds to the elements of what.
 *
 * <p>For a reader of a call that reads what the behavior answers where the call stands, with the
 * parameters standing for what the call handed. What the body binds is read in the body's own
 * module, which is where the declarations it names were written.
 *
 * @param body       the body, as the analysis of the behavior reads it
 * @param parameters the bindings a call hands its values to, in the order it hands them
 * @param elements   what the body binds to the elements of what ({@link ElementBindings})
 */
public record CalledBody(Core body, List<Core.Binder> parameters, ElementBindings elements) {

    public CalledBody {
        Objects.requireNonNull(body, "a behavior read at a call has a body");
        parameters = List.copyOf(parameters);
        Objects.requireNonNull(elements, "and binds what it binds, if nothing");
    }
}
