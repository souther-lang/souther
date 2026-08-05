package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * A declaration that says what it answers as well as what it takes.
 *
 * <p>The condition a call has to meet to be kept standing. A declaration may leave its result to its
 * body — most do, and nothing is wrong with that — but a call typed without expanding it has only
 * what the declaration says, so an operation a representation keeps must say all of it. The
 * requirement is on being kept, not on being a library function or a helper: it is the same
 * condition whichever namespace the name is in, because it is the same thing being asked of it.
 *
 * <p>A type rather than a check, so the incompleteness cannot travel. Were the result allowed to be
 * absent here, every reader of a kept call would have to answer for a result that is not there, and
 * the first one that did not would fail somewhere with nothing to say about which operation or which
 * representation was at fault.
 */
public record CompleteSignature(List<Type> params, Type result) {

    public CompleteSignature {
        params = List.copyOf(params);
    }

    /**
     * The signature {@code operation} was declared with, refusing one that leaves its result to its
     * body.
     *
     * <p>Raised where a representation says what it keeps, so an operation that cannot be typed
     * without expanding it is answered for once, by name, rather than as a failure at whichever call
     * happened to be reached first.
     */
    public static CompleteSignature of(ValueName operation, List<Type> params, Type result) {
        if (result == null) {
            throw new IllegalStateException("`" + operation + "` is kept standing by a representation"
                    + " that reads it, so it must declare what it answers: a call kept unexpanded is"
                    + " typed from its declaration alone");
        }
        return new CompleteSignature(params, result);
    }

}
