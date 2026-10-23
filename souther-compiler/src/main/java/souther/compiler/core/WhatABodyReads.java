package souther.compiler.core;

import souther.compiler.types.BindingId;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;

/**
 * Which names a tree reads, asked of the tree that runs.
 *
 * <p>One walk for the question a reader of a body asks of an expression: whether it reads a
 * binding anywhere inside it. A {@link Core.Read} says which binding it is, so a binding of the
 * same spelling further in is not the one asked about.
 */
public final class WhatABodyReads {

    private WhatABodyReads() {}

    /** Whether {@code e} reads the binding {@code binding} anywhere inside it. */
    public static boolean binding(Core e, BindingId binding) {
        if (e instanceof Core.Read read && read.binding().equals(binding)) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] = found[0] || binding(child, binding));
        return found[0];
    }

    /**
     * The names {@code read} reads, and the names the values {@code e} binds them to read, on
     * down: every name whose value goes into what {@code read} answers. Nothing where it is null.
     */
    public static Set<BindingId> namesReadBy(Core e, Core read) {
        Set<BindingId> out = new HashSet<>();
        if (read == null) {
            return out;
        }
        Map<BindingId, Core> values = new HashMap<>();
        boundIn(e, values);
        Deque<Core> left = new ArrayDeque<>(List.of(read));
        while (!left.isEmpty()) {
            readsIn(left.pop(), name -> {
                if (out.add(name) && values.containsKey(name)) {
                    left.push(values.get(name));
                }
            });
        }
        return out;
    }

    private static void boundIn(Core e, Map<BindingId, Core> values) {
        if (e instanceof Core.LetIn let && let.binder() != null
                && let.binder().binding() != null) {
            values.put(let.binder().binding(), let.value());
        }
        Core.forEachChild(e, child -> boundIn(child, values));
    }

    private static void readsIn(Core e, Consumer<BindingId> each) {
        if (e instanceof Core.Read read) {
            each.accept(read.binding());
        }
        Core.forEachChild(e, child -> readsIn(child, each));
    }

    /** Whether {@code read}, the one node, is {@code e} or anywhere inside it. */
    public static boolean holds(Core e, Core.Read read) {
        if (e == read) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] = found[0] || holds(child, read));
        return found[0];
    }

    /** Whether {@code e} reads any of {@code bindings} anywhere inside it. */
    public static boolean anyOf(Core e, Set<BindingId> bindings) {
        if (e instanceof Core.Read read && bindings.contains(read.binding())) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] = found[0] || anyOf(child, bindings));
        return found[0];
    }

    /**
     * {@code from}, and every name {@code e} binds to a value that reads one of them: what a read
     * of any of these reads of {@code from}, through the names inside {@code e} as well.
     */
    public static Set<BindingId> namesMadeOf(Core e, Set<BindingId> from) {
        Set<BindingId> out = new HashSet<>(from);
        madeOf(e, out);
        return out;
    }

    private static void madeOf(Core e, Set<BindingId> out) {
        if (e instanceof Core.LetIn let) {
            madeOf(let.value(), out);
            if (let.binder() != null && let.binder().binding() != null
                    && anyOf(let.value(), out)) {
                out.add(let.binder().binding());
            }
            madeOf(let.body(), out);
            return;
        }
        Core.forEachChild(e, child -> madeOf(child, out));
    }

    /** Whether {@code e} reads any binding anywhere inside it: a value that reads none is made of
     *  what is written in it alone. */
    public static boolean anyBinding(Core e) {
        if (e instanceof Core.Read) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] = found[0] || anyBinding(child));
        return found[0];
    }

    /**
     * That {@code e} reads {@code binding} nowhere inside it, as the walk {@link #binding} found
     * it — or empty where it reads it somewhere.
     */
    public static Optional<ReadsNothingOf> without(Core e, BindingId binding) {
        return binding(e, binding) ? Optional.empty() : Optional.of(new ReadsNothingOf(binding));
    }

    /**
     * That a tree was walked and reads {@code binding} nowhere inside it.
     *
     * <p>Made only by {@link #without}, after the walk, so holding one is that walk's answer and
     * not a claim about it. It keeps the binding and not the tree: what it answers is said once,
     * and a value holding it is compared by the binding alone.
     */
    public static final class ReadsNothingOf {

        private final BindingId binding;

        private ReadsNothingOf(BindingId binding) {
            this.binding = Objects.requireNonNull(binding, "a walk asks after some binding");
        }

        /** The binding the tree reads nowhere. */
        public BindingId binding() {
            return binding;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof ReadsNothingOf that && binding.equals(that.binding);
        }

        @Override
        public int hashCode() {
            return binding.hashCode();
        }

        @Override
        public String toString() {
            return "reads nothing of " + binding;
        }
    }
}
