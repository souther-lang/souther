package souther.compiler.coverage;

import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import java.util.Map;

/**
 * What each name of one body reads from, as a place rather than as a minted number.
 *
 * <p>Read off the one descent that worked out where the body's places are ({@link NodeAddresses}),
 * because a binder is at a slot of a node and the node is at an address. A walk of its own here
 * would be a second answer to what the body holds, with its own idea of what to make of a node
 * several ways lead to.
 */
final class Binders {

    private final String behavior;

    private final Map<BindingId, BinderAddress> byId;

    private Binders(String behavior, Map<BindingId, BinderAddress> byId) {
        this.behavior = behavior;
        this.byId = byId;
    }

    /** Where every binder of the body {@code places} was taken over stands. */
    static Binders of(NodeAddresses places) {
        return new Binders(places.behavior(), places.bound());
    }

    /**
     * Where {@code read} reads from.
     *
     * <p>Three answers and only two of them are places. A name the body binds is at the binder's
     * slot; a name it does not is the behavior's own parameter, which the signature bound and
     * numbered in the order it wrote them. Anything else is a read of a binding nothing in sight
     * opens, and there is no address to give it: the body would be saying it reads something no
     * reader of this could find, and answering with a made-up place would put that in a value.
     */
    BinderAddress at(BindingId read) {
        BinderAddress local = byId.get(read);
        if (local != null) {
            return local;
        }
        // The declaration this body is of, which is what binds a parameter and numbered the
        // parameters in the order it wrote them. Told by the name it declares and not by the module
        // beside it: which module a plan is labelled with is the caller's word for a collection of
        // bodies, and a body is this behavior's because it is the body this walk was handed under
        // that name.
        if (read.owner() instanceof BindingOwner.OfValue declared
                && declared.name().equals(behavior)) {
            return new BinderAddress.Parameter(behavior, read.ordinal());
        }
        throw new IllegalStateException("`" + behavior + "` reads " + read
                + ", which nothing in its body binds and its signature does not name");
    }
}
