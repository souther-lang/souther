package souther.compiler.core;

import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What a checked {@link Core.Block} reaches outside its own lexical boundary, in the three kinds an
 * output tells apart: a binding of the enclosing body it reads, a declaration it calls, and a
 * behavior it calls that the block's own construction requires injected.
 *
 * <p>A lexical fact and not a closure layout. Nested blocks, {@code let}, a {@code match} arm's
 * binder and an attempted construction's binder all narrow what counts as outside, and this walks
 * that scoping once so every backend answers the same question about the same tree rather than
 * rediscovering it. Which of these an output has to carry physically — a field, a captured cell, an
 * environment slot — and which it can leave to be resolved statically is an output's own decision;
 * this says only what is reached.
 *
 * <p>Each list is first-seen order, because that order is the constructor or slot layout a reader
 * builds from — a set whose type did not say it was ordered would leave that promise nowhere.
 * {@code requirements} is not a subset of {@code declarations}: which behaviors a construction
 * requires injected is a relation between the enclosing behavior and its callee (ADR-0068), not a
 * property of the callee alone, so a caller hands the requirements in scope over rather than this
 * working it out from the callee by itself.
 */
public record BlockReaches(
        List<Core.Read> bindings,
        List<Core.Reached> declarations,
        List<ValueName.Behavior> requirements) {

    /**
     * What {@code block}'s body reaches outside itself, given the behaviors {@code block}'s
     * enclosing construction requires injected.
     */
    public static BlockReaches of(Core.Block block, Set<ValueName.Behavior> requirementsInScope) {
        Accumulator acc = new Accumulator(requirementsInScope);
        Set<BindingId> bound = new HashSet<>();
        block.params().forEach(p -> bound.add(p.binding()));
        walk(block.body(), bound, acc);
        return new BlockReaches(List.copyOf(acc.bindings.values()),
                List.copyOf(acc.declarations), List.copyOf(acc.requirements));
    }

    private static final class Accumulator {
        private final Set<ValueName.Behavior> requirementsInScope;
        private final LinkedHashMap<BindingId, Core.Read> bindings = new LinkedHashMap<>();
        private final LinkedHashSet<Core.Reached> declarations = new LinkedHashSet<>();
        private final LinkedHashSet<ValueName.Behavior> requirements = new LinkedHashSet<>();

        private Accumulator(Set<ValueName.Behavior> requirementsInScope) {
            this.requirementsInScope = requirementsInScope;
        }
    }

    private static void walk(Core e, Set<BindingId> bound, Accumulator acc) {
        switch (e) {
            case Core.PreservedCall p -> throw p.unexpectedIn("what a block reaches");
            case Core.Read read -> {
                if (!bound.contains(read.binding())) {
                    acc.bindings.putIfAbsent(read.binding(), read);
                }
            }
            case Core.Call c -> {
                reached(c, acc);
                c.args().forEach(a -> walk(a, bound, acc));
            }
            case Core.Apply a -> {
                walk(a.fn(), bound, acc);
                a.args().forEach(x -> walk(x, bound, acc));
            }
            case Core.FieldAccess fa -> walk(fa.target(), bound, acc);
            case Core.Binary bin -> {
                walk(bin.left(), bound, acc);
                walk(bin.right(), bound, acc);
            }
            case Core.Neg neg -> walk(neg.operand(), bound, acc);
            case Core.Construct nd -> nd.values().forEach(v -> walk(v.value(), bound, acc));
            case Core.If iff -> {
                walk(iff.cond(), bound, acc);
                walk(iff.then(), bound, acc);
                walk(iff.els(), bound, acc);
            }
            case Core.IfConstructed ic -> {
                walk(ic.construct(), bound, acc);
                enter(bound, ic.binder().binding(), () -> walk(ic.then(), bound, acc));
                ic.els().forEach(arm -> walk(arm.body(), bound, acc));
            }
            case Core.LetIn li -> {
                walk(li.value(), bound, acc);
                enter(bound, li.binder().binding(), () -> walk(li.body(), bound, acc));
            }
            case Core.Match m -> {
                walk(m.scrutinee(), bound, acc);
                for (Core.Case c : m.cases()) {
                    if (c.binder() == null) {
                        walk(c.body(), bound, acc);
                    } else {
                        enter(bound, c.binder().binding(), () -> walk(c.body(), bound, acc));
                    }
                }
            }
            case Core.Block b -> {
                List<BindingId> entered = b.params().stream().map(Core.Binder::binding).toList();
                entered.forEach(bound::add);
                walk(b.body(), bound, acc);
                entered.forEach(bound::remove);
            }
            case Core.ListLit lit -> lit.elements().forEach(x -> walk(x, bound, acc));
            case Core.OptionSome so -> walk(so.value(), bound, acc);
            case Core.Tuple t -> t.elements().forEach(x -> walk(x, bound, acc));
            case Core.TupleGet tg -> walk(tg.tuple(), bound, acc);
            case Core.OptionNone _ -> { }
            case Core.Int _ -> { }
            case Core.Decimal _ -> { }
            case Core.Str _ -> { }
            case Core.Bool _ -> { }
            case Core.Temporal _ -> { }
            case Core.Unreachable _ -> { }
            case Core.UnitValue _ -> { }
            case Core.MaterialisedValue m -> throw new IllegalStateException(
                    "the tree this walks holds no build of a value, and this holds one of "
                            + m.value());
        }
    }

    /** {@code call} named an external declaration: it goes to {@code requirements} where it denotes
     *  a behavior this block's construction requires injected, and to {@code declarations}
     *  otherwise. {@link Core.Emitted}, the other arm a call may reach, names no declaration and is
     *  not an external reach. */
    private static void reached(Core.Call call, Accumulator acc) {
        if (!(call.fn() instanceof Core.Reached reached)) {
            return;
        }
        if (reached.denotes() instanceof ValueName.Behavior behavior
                && acc.requirementsInScope.contains(behavior)) {
            acc.requirements.add(behavior);
        } else {
            acc.declarations.add(reached);
        }
    }

    /**
     * Walks {@code body} with {@code binding} added to {@code bound}, then takes it back out.
     *
     * <p>A DFS backtracks: no branch this returns to ever needed a scope another branch entered, so
     * one shared, mutated set answers every scope along the walk. A copy per {@code let}, arm or
     * nested block instead would sum to the square of how deep the scopes nest, for a cost this walk
     * never needs to pay.
     */
    private static void enter(Set<BindingId> bound, BindingId binding, Runnable body) {
        bound.add(binding);
        body.run();
        bound.remove(binding);
    }
}
