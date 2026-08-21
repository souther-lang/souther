package souther.compiler.inputs;

import souther.compiler.check.Shape;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What stands directly under a type, and nothing else.
 *
 * <p>The one step two readers of one structure take. What positions a behavior's input has and
 * where a value has to be built are different questions about the same fields, and each had a
 * recursion of its own, kept in step by hand and already out of step about how deep to go, about
 * whether a shape outside the readable set is refused, and about whether a path is a
 * {@link TermPath} or a string. A third reader of that question would have written a third.
 *
 * <p><b>One step and no walk.</b> What is under a type is a fact about the type. How far down to
 * follow it, where to stop because the caller has already settled something, and what type stands at
 * a path once a construction recipe has chosen one are not facts about the type: they belong to
 * whoever is asking, and each of them lives in the reader that has a use for it. Handed here as
 * settings they would make this the thing that decides which positions there are, with a caller's
 * argument deciding which set it answers — which is the shape this exists to remove rather than to
 * hold one level up.
 *
 * <p>So there is no depth here, no stop, no recipe, and nothing of what either reader does with the
 * answer. {@link InputDomain} reads what the declaration says an input has; the generator refines a
 * declared position into one a value is built at and asks again. Both take their steps from here and
 * neither takes the other's meaning with it.
 */
public final class StructuralDescent {

    /**
     * The positions directly under one, and the name of the product they are the fields of.
     *
     * @param of    what the product is called, which is what a value built out of these is written
     *              as
     * @param under the fields, in the order the declaration writes them — which is the order they
     *              are walked, reported and composed in
     */
    public record Children(TypeSymbol of, Map<String, Type> under) {

        public Children {
            under = java.util.Collections.unmodifiableMap(new LinkedHashMap<>(under));
        }
    }

    /**
     * What is under a position of this shape, or null where it is not made of positions.
     *
     * <p>Null and not an empty {@link Children}: a record declaring no fields is made of positions
     * and has none, and a type that is not a record is not made of positions at all. The two are
     * different answers and each reader treats them differently.
     */
    public static Children of(Shape shape) {
        return shape instanceof Shape.Product product
                ? new Children(product.name(), product.fields()) : null;
    }

    private StructuralDescent() {}
}
