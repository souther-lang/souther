package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Which of a body's bindings hold an element of a container, and of which container.
 *
 * <p>A fact about the program and not about any reader of it. What a standard-library operation
 * hands its closure is stated by the library's own signature ({@link Combinators}); this is that
 * statement made about one body's bindings, at the one point in the pipeline where it can still be
 * read.
 *
 * <p><b>Taken before the relation is erased, and not recovered afterwards.</b> The tree the backend
 * emits from has no combinator left in it: a fold that only grows a collection is rewritten into a
 * walk over a builder, and two such walks in a row are joined into one, so what handed a closure an
 * element is gone and which closure a value came from is no longer a question the tree answers. A
 * reader downstream of that has to recognise the shapes the rewrite happens to produce, which makes
 * the set of combinators it can read a consequence of an optimisation — and the day the optimisation
 * learns a new shape, the reading narrows with nothing saying so.
 *
 * <p>So the relation is read where it stands and carried by binding. What survives the rewrite is
 * the binding: it renames nothing, so a fact keyed this way is as true after it as before. Nothing
 * here is recovered by matching one tree against another, and no identity is invented for the
 * purpose — {@link BindingId} already tells one occurrence from another, which is exactly what a
 * helper expanded at two call sites needs and exactly what the construct an author wrote must not be
 * asked to do.
 *
 * <p>What a binding holds is kept as the expression it was read from rather than as a position.
 * Which position that expression names is a question about a behavior's declared input, and a
 * container is not always one — it can be what another operation answered, which is where a reading
 * of provenance goes on rather than stopping ({@link ElementLineage}).
 */
public record ElementBindings(Map<BindingId, Core> containers) {

    /** Nothing was read, which is what a body with no combinator in it comes to. */
    public static final ElementBindings NONE = new ElementBindings(Map.of());

    public ElementBindings {
        containers = Map.copyOf(containers);
    }

    /** The container an element at {@code binding} was taken from, or null where the binding holds
     *  something else. */
    public Core containerOf(BindingId binding) {
        return binding == null ? null : containers.get(binding);
    }

    public boolean isEmpty() {
        return containers.isEmpty();
    }

    /**
     * What {@code body} binds to the elements of what.
     *
     * <p>Read off the signatures and the tree together: which argument holds the container and which
     * of the closure's parameters the element arrives on is {@link Combinators}' answer about the
     * operation, and which bindings those are is this tree's.
     *
     * <p>A closure written as anything but a block is not read. What such an argument stands for is a
     * value some other binding holds, and the parameter an element arrives on is that value's, not
     * this call's to name.
     */
    public static ElementBindings of(Core body) {
        Map<BindingId, Core> found = new LinkedHashMap<>();
        walk(body, found);
        return found.isEmpty() ? NONE : new ElementBindings(found);
    }

    private static void walk(Core e, Map<BindingId, Core> found) {
        if (e instanceof Core.Call call
                && call.fn() instanceof Core.Reached reached) {
            Combinators.Combinator handed = Combinators.of(reached.denotes());
            if (handed != null
                    && handed.closureArg() < call.args().size()
                    && handed.containerArg() < call.args().size()
                    && call.args().get(handed.closureArg()) instanceof Core.Block step
                    && handed.elementParam() < step.params().size()) {
                BindingId element = step.params().get(handed.elementParam()).binding();
                if (element != null) {
                    // The nearest binding of a name stands, as everywhere else: a body binding one
                    // twice has two bindings, and each is answered where it is.
                    found.putIfAbsent(element, call.args().get(handed.containerArg()));
                }
            }
        }
        Core.forEachChild(e, child -> walk(child, found));
    }
}
