package souther.compiler.inputs;

import souther.compiler.types.BindingId;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Supplier;

/**
 * The bindings a reading of where a value came from is inside, so that a walk over the binding graph
 * stops where it arrives at one it is already answering.
 *
 * <p>The whole of what stops such a walk. Everything else it does descends an expression — a field's
 * target, a call's argument, a {@code let}'s body — and a tree is finite, so a step that stays
 * inside one is a step nothing has to bound. What crosses to another expression is a binding: what a
 * name holds, what handed a name the elements of a container, which binding another's elements are
 * the same as. Those steps are the graph, and this is where the graph is kept acyclic.
 *
 * <p><b>The way here and not the ways gone.</b> A binding leaves the trail when the walk that
 * entered it comes back, so two attempts one after the other are two walks and neither is the
 * other's cycle: a name is answered for by what it holds, and where that reaches no position, by
 * being an element of a container — the same binding, twice, along different ways. A set that only
 * grew would refuse the second for having been to the first, and the answer would depend on which
 * order the attempts happen to be written in.
 *
 * <p>What a cycle is, is that this compiler's own representation is not what it says it is. What is
 * violated is not that a binding holds one value — two bindings holding each other hold one value
 * each — but that the lineage built here runs one way: what a name holds is worked out where the
 * name was written, from what stood before it, and the record of which binding another's elements
 * came from is written where the operation that made them still stood. A walk that arrives back at
 * a binding it is answering has been handed a graph nothing here builds.
 *
 * <p>So it is raised rather than reported. A walk that answered "no position" for it would say of a
 * model that it states no rule where a position, and a reader has no way to tell that from a model
 * that states none.
 */
final class BindingTrail {

    private final Set<BindingId> active = new HashSet<>();

    /**
     * {@code answer}, worked out with {@code binding} on the way.
     *
     * <p>Wrapped around the step rather than checked before it, so that leaving is not something a
     * caller can forget on the way out of an arm.
     */
    <T> T through(BindingId binding, Supplier<T> answer) {
        if (!active.add(binding)) {
            throw new ReadThroughItself(binding);
        }
        try {
            return answer.get();
        } finally {
            active.remove(binding);
        }
    }

    /** A binding whose value is read through the binding itself. */
    static final class ReadThroughItself extends IllegalStateException {

        private static final long serialVersionUID = 1L;

        ReadThroughItself(BindingId binding) {
            super("the value of " + binding + " is read through " + binding);
        }
    }
}
