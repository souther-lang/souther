package souther.compiler.coverage;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What each name of one body reads from, as a place rather than as a minted number.
 *
 * <p>Built with the addresses of the body's own places, because that is what a binder standing in it
 * is named by. Asked once per body and read by whatever is writing the body down in a form two
 * compiles can be held against each other by.
 */
final class Binders {

    private final String behavior;

    private final Map<BindingId, BinderAddress> byId = new LinkedHashMap<>();

    private Binders(String behavior) {
        this.behavior = behavior;
    }

    /** Where every binder of {@code body} stands, {@code body} being {@code behavior}'s. */
    static Binders of(String behavior, Core body, NodeAddresses places) {
        Binders out = new Binders(behavior);
        out.walk(body, places);
        return out;
    }

    private void walk(Core at, NodeAddresses places) {
        switch (at) {
            case Core.LetIn li ->
                    put(li.binder(), places.of(li), new BinderSlot.LetBinder());
            case Core.Block b -> {
                for (int i = 0; i < b.params().size(); i++) {
                    put(b.params().get(i), places.of(b), new BinderSlot.BlockParam(i));
                }
            }
            case Core.Match m -> {
                for (int i = 0; i < m.cases().size(); i++) {
                    put(m.cases().get(i).binder(), places.of(m), new BinderSlot.CaseBinder(i));
                }
            }
            case Core.IfConstructed ic ->
                    put(ic.binder(), places.of(ic), new BinderSlot.ConstructedBinder());
            default -> { }
        }
        for (CoreStructure.Child child : CoreStructure.childrenOf(at)) {
            walk(child.node(), places);
        }
    }

    private void put(Core.Binder binder, NodeAddress owner, BinderSlot slot) {
        if (binder == null || binder.binding() == null) {
            return;   // a slot the node has and this body left empty
        }
        // One binder per place, so a second answer for one id is a body binding one name twice —
        // which the reads under it could not tell apart either.
        BinderAddress already = byId.put(binder.binding(), new BinderAddress.Local(owner, slot));
        if (already != null) {
            throw new IllegalStateException("`" + behavior + "` binds " + binder.binding()
                    + " at " + already + " and again at " + byId.get(binder.binding()));
        }
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
