package souther.compiler.coverage;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.IntFunction;

/**
 * Which slot of a node each of its children stands in, named.
 *
 * <p>What a place in a body is addressed by. A node is where it is because of the way down to it —
 * the right of a {@code ++} rather than the left, the second case of a {@code match} rather than the
 * first — and until something says which way each step went, the only thing that tells two places
 * apart is the object standing at them. That is enough for a walk holding the tree and no use at all
 * to anything comparing two walks, which is what a numbering has to be compared by.
 *
 * <p>{@link Core#forEachChild} hands children over without saying where they came from: the three
 * operators under it separate an expression slot from a name slot and a construction slot, and
 * nothing separates {@code then} from {@code else}. So this is beside it rather than built on it.
 *
 * <p>Not a general facility for the compiler. What is named here is what an address of one place in
 * one body needs, and the vocabulary is this package's because that is the question it answers. A
 * pass wanting to rewrite children has {@code Core.mapChildren}, which is about slots and not about
 * where they are.
 *
 * <p><b>One edge apiece.</b> No node hands over two children under one {@link Edge}, which is what
 * lets an edge and a node stand for a step down. The switch is over a sealed type, so a node kind
 * added to the IR arrives here as a compile error rather than as a place nothing can address.
 */
public final class CoreStructure {

    /** Which slot of its parent a child stands in. */
    public sealed interface Edge {

        record NegOperand() implements Edge {}

        record FieldTarget() implements Edge {}

        record BinaryLeft() implements Edge {}

        record BinaryRight() implements Edge {}

        record CallArgument(int index) implements Edge {}

        record PreservedArgument(int index) implements Edge {}

        /** The binding an {@code Apply} loads what it applies from, which is a name and not an
         *  expression. */
        record AppliedFunction() implements Edge {}

        record ApplyArgument(int index) implements Edge {}

        record IfCondition() implements Edge {}

        record IfThen() implements Edge {}

        record IfElse() implements Edge {}

        /** The construction an attempt tests, which is where its condition is. */
        record ConstructedAttempt() implements Edge {}

        record ConstructedThen() implements Edge {}

        record ConstructedElse(int index) implements Edge {}

        record LetValue() implements Edge {}

        record LetBody() implements Edge {}

        record BlockBody() implements Edge {}

        record ListElement(int index) implements Edge {}

        record SomeValue() implements Edge {}

        record TupleElement(int index) implements Edge {}

        /** The tuple a {@code TupleGet} reads from. */
        record TupleSource() implements Edge {}

        record FieldValue(int index) implements Edge {}

        record MatchScrutinee() implements Edge {}

        record MatchCase(int index) implements Edge {}
    }

    /** One step down: the slot, and what stands in it. */
    record Child(Edge edge, Core node) {

        Child {
            if (edge == null || node == null) {
                throw new IllegalArgumentException("a step down is a slot and what is in it");
            }
        }
    }

    /**
     * The children of {@code e}, each with the slot it stands in, in the order the node holds them.
     *
     * <p>Exhaustive, and the leaves answer with nothing rather than being left out of the switch: a
     * node kind that answers no children is a decision about that kind, and one that fell through a
     * default would be a place a walk stopped without anyone saying so.
     */
    static List<Child> childrenOf(Core e) {
        List<Child> out = new ArrayList<>();
        switch (e) {
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _,
                 Core.Read _, Core.UnitValue _, Core.OptionNone _, Core.Unreachable _ -> { }
            case Core.Neg n -> out.add(new Child(new Edge.NegOperand(), n.operand()));
            case Core.FieldAccess fa -> out.add(new Child(new Edge.FieldTarget(), fa.target()));
            case Core.Binary b -> {
                out.add(new Child(new Edge.BinaryLeft(), b.left()));
                out.add(new Child(new Edge.BinaryRight(), b.right()));
            }
            case Core.Call c -> indexed(out, c.args(), Edge.CallArgument::new);
            case Core.PreservedCall p -> indexed(out, p.args(), Edge.PreservedArgument::new);
            case Core.Apply a -> {
                out.add(new Child(new Edge.AppliedFunction(), a.fn()));
                indexed(out, a.args(), Edge.ApplyArgument::new);
            }
            case Core.If iff -> {
                out.add(new Child(new Edge.IfCondition(), iff.cond()));
                out.add(new Child(new Edge.IfThen(), iff.then()));
                out.add(new Child(new Edge.IfElse(), iff.els()));
            }
            case Core.IfConstructed ic -> {
                out.add(new Child(new Edge.ConstructedAttempt(), ic.construct()));
                out.add(new Child(new Edge.ConstructedThen(), ic.then()));
                for (int i = 0; i < ic.els().size(); i++) {
                    out.add(new Child(new Edge.ConstructedElse(i), ic.els().get(i).body()));
                }
            }
            case Core.LetIn li -> {
                out.add(new Child(new Edge.LetValue(), li.value()));
                out.add(new Child(new Edge.LetBody(), li.body()));
            }
            case Core.Block b -> out.add(new Child(new Edge.BlockBody(), b.body()));
            case Core.ListLit lit -> indexed(out, lit.elements(), Edge.ListElement::new);
            case Core.OptionSome s -> out.add(new Child(new Edge.SomeValue(), s.value()));
            case Core.Tuple t -> indexed(out, t.elements(), Edge.TupleElement::new);
            case Core.TupleGet tg -> out.add(new Child(new Edge.TupleSource(), tg.tuple()));
            case Core.Construct nd -> {
                for (int i = 0; i < nd.values().size(); i++) {
                    out.add(new Child(new Edge.FieldValue(i), nd.values().get(i).value()));
                }
            }
            case Core.Match m -> {
                out.add(new Child(new Edge.MatchScrutinee(), m.scrutinee()));
                for (int i = 0; i < m.cases().size(); i++) {
                    out.add(new Child(new Edge.MatchCase(i), m.cases().get(i).body()));
                }
            }
        }
        return List.copyOf(out);
    }

    /**
     * The children of one node, handed over a slot at a time to a walk that names each as it goes.
     *
     * <p>For a walk that has to descend the slots itself — because it is deciding something at each
     * of them and not only visiting them — and must still be held to the children the node has. It
     * says which slot it is taking and which node it believes is in it, and this is what says both
     * are right; {@link #requireExhausted()} at the end is what says none was left.
     *
     * <p>So the walk keeps its own reason for going where it goes, and stops being the second place
     * that says which slots a node has.
     */
    static final class Children {

        private final Core of;

        private final List<Child> children;

        /** The same children, by slot. One edge apiece, so a slot is looked up rather than
         *  searched for: a list literal has as many slots as it has elements, and a scan per
         *  step down is a walk quadratic in the width of the node it is walking. */
        private final Map<Edge, Child> bySlot;

        private final Set<Edge> taken = new HashSet<>();

        private Children(Core of, List<Child> children) {
            this.of = of;
            this.children = children;
            Map<Edge, Child> bySlot = new HashMap<>();
            children.forEach(child -> bySlot.put(child.edge(), child));
            this.bySlot = bySlot;
        }

        /** The children of {@code e}, to be taken a slot at a time. */
        static Children of(Core e) {
            return new Children(e, childrenOf(e));
        }

        /**
         * The node in {@code edge}, which the caller says is {@code expected}.
         *
         * <p>Three ways to be wrong and all of them loud: a slot this node has none of, a slot
         * already taken, and a slot holding something other than what the caller reached for. The
         * last is what a walk descending by hand gets wrong — the left of a comparison walked as
         * the right — and it is the one nothing else here would notice.
         */
        Core take(Edge edge, Core expected) {
            Child child = bySlot.get(edge);
            if (child == null) {
                throw new IllegalStateException("a " + of.getClass().getSimpleName() + " at "
                        + of.pos() + " has no " + edge + "; its slots are "
                        + children.stream().map(Child::edge).toList());
            }
            if (!taken.add(edge)) {
                throw new IllegalStateException("the " + edge + " of a "
                        + of.getClass().getSimpleName() + " at " + of.pos()
                        + " was taken twice");
            }
            if (child.node() != expected) {
                throw new IllegalStateException("the " + edge + " of a "
                        + of.getClass().getSimpleName() + " at " + of.pos()
                        + " holds something other than what the walk reached for");
            }
            return child.node();
        }

        /**
         * That every slot was taken.
         *
         * <p>What stops a walk from quietly going nowhere. A node kind that grows a child is a
         * compile error in the switch above and nothing in the walk; without this the walk would go
         * on visiting what it always did and the new child would be somewhere nothing looks.
         */
        void requireExhausted() {
            if (taken.size() != children.size()) {
                List<Edge> missed = new ArrayList<>();
                children.forEach(child -> {
                    if (!taken.contains(child.edge())) {
                        missed.add(child.edge());
                    }
                });
                throw new IllegalStateException("a walk of a " + of.getClass().getSimpleName()
                        + " at " + of.pos() + " went nowhere near " + missed);
            }
        }
    }

    private static void indexed(List<Child> out, List<Core> children,
                                IntFunction<Edge> slot) {
        for (int i = 0; i < children.size(); i++) {
            out.add(new Child(slot.apply(i), children.get(i)));
        }
    }

    private CoreStructure() {}
}
