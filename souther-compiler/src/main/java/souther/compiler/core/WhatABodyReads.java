package souther.compiler.core;

import souther.compiler.types.BindingId;

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
}
