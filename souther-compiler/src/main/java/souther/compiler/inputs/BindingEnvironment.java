package souther.compiler.inputs;

import souther.compiler.check.ElementBindings;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What is known of the names in a tree, as answers to the questions a walk over them asks.
 *
 * <p>Two readings are built out of this and they are not the same reading. What a name stands for
 * ({@link ReadMeaning}) is one, and which position of the input an expression reaches
 * ({@link InputPath}) is the other; the first is written in terms of the second, and both are
 * written in terms of what is here.
 *
 * <p><b>Facts and never an answer.</b> A reading held here would be reachable from the reading built
 * on it, and the two would call each other: what a name means is worked out by asking which position
 * it reaches, so a walk after a position that could ask what a name means would be asking a question
 * whose answer it is. Kept to facts, that is not something a caller can write.
 *
 * <p><b>And the facts themselves do not come back.</b> Which of them wins where a binding is more
 * than one of them, and what an edge between two bindings' elements licenses, are decisions with one
 * place each ({@link BindingRole}, {@link souther.compiler.check.ElementProvenance#stepFrom}) —
 * and a caller holding the tables would be free to make them again, in an order or with a licence of
 * its own. So what is published is the questions, and the tables are not among them.
 *
 * <p>Which is also what keeps a traversal from measuring itself against the environment. How many
 * names are known here is not how far a value's provenance runs — a name bound in one arm is read
 * under bindings written elsewhere — and there is nothing to count with: what stops a walk over
 * these facts is where it has been ({@link BindingTrail}), never how much there is.
 *
 * <p>A value, compared by what it holds. It travels inside a reading, which is compared the same
 * way, and an identity that told two equal environments apart would make a name's meaning depend on
 * which copy of them a caller had.
 */
final class BindingEnvironment {

    /**
     * How many bindings are kept beside the table before they are written into a new one.
     *
     * <p>Going inside a binding is done once for every {@code let} between a walk's start and the
     * name it asks about, so the cost of one is the cost of a chain of them squared. A table copied
     * at each is what that square is made of; a few kept apart and searched newest first are what
     * keeps a lookup as short as the number kept, and the table is copied once for that many.
     */
    private static final int KEPT_APART = 16;

    /** One binding made on the way here, over the ones made before it. */
    private record Layer(BindingId binding, Core value, Layer older, int depth) {}

    private final Map<BindingId, TermPath> roots;
    private final Map<BindingId, Core> table;
    private final Layer newest;
    private final ElementBindings elements;
    private final boolean callsStand;
    private volatile Map<BindingId, Core> boundAsATable;

    BindingEnvironment(Map<BindingId, TermPath> roots, Map<BindingId, Core> bound,
                       ElementBindings elements, boolean callsStand) {
        this(Map.copyOf(roots), Map.copyOf(bound), null, elements, callsStand);
    }

    private BindingEnvironment(Map<BindingId, TermPath> roots, Map<BindingId, Core> table,
                               Layer newest, ElementBindings elements, boolean callsStand) {
        this.roots = roots;
        this.table = table;
        this.newest = newest;
        this.elements = elements;
        this.callsStand = callsStand;
    }

    /** What {@code binding} is bound to on the way here, the nearest binding winning. */
    private Core boundTo(BindingId binding) {
        for (Layer layer = newest; layer != null; layer = layer.older()) {
            if (layer.binding().equals(binding)) {
                return layer.value();
            }
        }
        return table.get(binding);
    }

    /** Everything bound on the way here as one table, made when it is asked for. */
    private Map<BindingId, Core> bound() {
        Map<BindingId, Core> made = boundAsATable;
        if (made == null) {
            if (newest == null) {
                made = table;
            } else {
                Map<BindingId, Core> wider = new LinkedHashMap<>(table);
                List<Layer> oldestFirst = new ArrayList<>();
                for (Layer layer = newest; layer != null; layer = layer.older()) {
                    oldestFirst.add(layer);
                }
                for (int at = oldestFirst.size() - 1; at >= 0; at--) {
                    wider.put(oldestFirst.get(at).binding(), oldestFirst.get(at).value());
                }
                made = Map.copyOf(wider);
            }
            boundAsATable = made;
        }
        return made;
    }

    /**
     * Where {@code binding} came from, as the one ordering of the facts held here
     * ({@link BindingRole}).
     *
     * <p>Every reader of these facts asks this rather than the three of them, so that which of them
     * wins is settled once. Read separately, the winner is whichever the reader looked at first, and
     * a binding that is more than one of these — a closure parameter of a walk joined to the one
     * before it is handed an element and bound to what the earlier closure made — comes back
     * differently to each of them.
     */
    BindingRole roleOf(BindingId binding) {
        TermPath root = roots.get(binding);
        if (root != null) {
            return new BindingRole.Root(root);
        }
        List<Core> containers = elements.containersOf(binding);
        if (containers.size() == 1) {
            return new BindingRole.Element(containers.get(0));
        }
        if (containers.size() > 1) {
            return new BindingRole.ElementOfSeveral(containers);
        }
        Core value = boundTo(binding);
        return value == null ? new BindingRole.Unknown() : new BindingRole.Alias(value);
    }

    /** Where in the element handed to {@code binding} the value a walk answered stands, or null
     *  where the walk answered no place of it ({@link ElementProjection}). */
    ElementProjection projectionAt(BindingId binding) {
        return elements.projectionAt(binding);
    }

    /**
     * What {@code binding} was bound to, wherever in the body it was bound, or null where nothing
     * bound it.
     *
     * <p>Beside {@link #roleOf} and not one of the facts it orders. That one answers what a name
     * means where it is read, and the way to a name is the way this walk came; this answers where a
     * container's elements are, and a container built by one operation and handed to the next is
     * bound beside the closure that reads it rather than above it — so the way to it is not the way
     * here. Read for that one question ({@link InputPath}) and for no other: given to a reader after
     * what a name means, it would answer with a binding the reader never passed.
     */
    Core heldAnywhereBy(BindingId binding) {
        // What is bound on the way here first, and what the body bound anywhere after it. No
        // binding holds nothing — this environment refuses a null value — so what is not here is
        // absent rather than bound to nothing, and one lookup says so.
        Core here = boundTo(binding);
        return here != null ? here : elements.boundTo(binding);
    }

    /**
     * What a walk asking {@code question} may do at {@code binding} ({@link ElementStep}).
     *
     * <p>The edge itself does not come back. What one licenses depends on what is being asked, and a
     * walk that held an edge would be answering that for itself beside the one place that answers it
     * ({@link souther.compiler.check.ElementProvenance#stepFrom}).
     */
    ElementStep stepFrom(BindingId binding, ElementQuestion question) {
        return elements.provenance().stepFrom(binding, question);
    }

    /**
     * Whether an operation the language defines the meaning of is left standing in this tree.
     *
     * <p>It is in the representation a declaration's own rules are read in and it is not in the one
     * that runs. A call left standing names no location, which is an answer where such a tree is
     * what was handed over and a fault in the caller where it is not.
     */
    boolean callsStand() {
        return callsStand;
    }

    /** The same, inside what {@code binder} binds. */
    BindingEnvironment inside(Core.Binder binder, Core value) {
        if (binder == null || binder.binding() == null || value == null) {
            return this;
        }
        // The nearest binding wins, which is what being inside it means.
        int depth = newest == null ? 1 : newest.depth() + 1;
        // A name given a build of a value holds what the value is.
        Layer inner = new Layer(binder.binding(), elements.dereferenced(value), newest, depth);
        if (depth <= KEPT_APART) {
            return new BindingEnvironment(roots, table, inner, elements, callsStand);
        }
        BindingEnvironment written = new BindingEnvironment(roots, table, inner, elements,
                callsStand);
        return new BindingEnvironment(roots, written.bound(), null, elements, callsStand);
    }

    /** The same, with {@code binding} standing at {@code path}. */
    BindingEnvironment naming(BindingId binding, TermPath path) {
        Map<BindingId, TermPath> wider = new LinkedHashMap<>(roots);
        wider.put(binding, path);
        return new BindingEnvironment(Map.copyOf(wider), table, newest, elements, callsStand);
    }

    /** The parameters as positions, which is what a name in a tree stands for. */
    static Map<BindingId, TermPath> rooted(Map<BindingId, String> named) {
        Map<BindingId, TermPath> out = new LinkedHashMap<>();
        named.forEach((binding, name) -> out.put(binding, TermPath.of(name)));
        return out;
    }

    @Override
    public boolean equals(Object other) {
        return this == other
                || (other instanceof BindingEnvironment that
                        && callsStand == that.callsStand
                        && roots.equals(that.roots)
                        && bound().equals(that.bound())
                        && elements.equals(that.elements));
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(roots, bound(), elements, callsStand);
    }

    @Override
    public String toString() {
        return "BindingEnvironment[roots=" + roots + ", bound=" + bound() + ", elements=" + elements
                + ", callsStand=" + callsStand + "]";
    }
}
