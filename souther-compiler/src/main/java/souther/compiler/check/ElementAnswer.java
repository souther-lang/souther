package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.semantics.Combinator;
import souther.compiler.types.BindingId;

/**
 * What a closure handed the elements of a walk answered, with the parameter it was written about.
 *
 * <p>Held only for a closure a licence stands behind: the walk answers one value per element of the
 * container it was handed, which is what makes the answer for each element the closure's answer on
 * it. What is read of the body is the reader's — one that wants a place of the element asks
 * {@link ElementBindings#projectionAt}, and one that wants what was computed from it reads this —
 * so the body is kept as the expression it was and not as any one reading of it.
 *
 * @param parameter the binding the closure was written about, which the body reads the element by
 * @param body      what the closure answered
 * @param position  the binding the closure is handed the element's position on, counted from nought
 *                  in the order the walked container holds its elements — or null where the
 *                  operation is shown to hand it none ({@link Combinator#positionParam})
 */
public record ElementAnswer(BindingId parameter, Core body, BindingId position) {

    public ElementAnswer {
        if (parameter == null || body == null) {
            throw new IllegalArgumentException("an answer is a closure's body about its parameter");
        }
    }
}
