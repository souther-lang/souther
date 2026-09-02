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

    /** The declaration this body is of, which is what binds its parameters. Module and name
     *  together, because that is what tells one owner from another: two modules declaring
     *  {@code f} own different bindings, so a read of the other module's would be taken for this
     *  behavior's parameter if only the name were compared. */
    private final BindingOwner.OfValue signature;

    private final Map<BindingId, BinderAddress> byId;

    private Binders(String module, String behavior, Map<BindingId, BinderAddress> byId) {
        this.behavior = behavior;
        this.signature = new BindingOwner.OfValue(module, behavior);
        this.byId = byId;
    }

    /** Where every binder of the body {@code places} was taken over stands, that body being the one
     *  {@code module} declares under the name the addresses are of. */
    static Binders of(String module, NodeAddresses places) {
        return new Binders(module, places.behavior(), places.bound());
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
        // The declaration this body is of, which binds its parameters and numbered them in the
        // order it wrote them.
        if (signature.equals(read.owner())) {
            return new BinderAddress.Parameter(behavior, read.ordinal());
        }
        throw new IllegalStateException("`" + behavior + "` reads " + read
                + ", which nothing in its body binds and its signature does not name");
    }
}
