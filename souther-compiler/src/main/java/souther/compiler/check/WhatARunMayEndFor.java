package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.abort.AbortSites;
import souther.compiler.core.Core;
import souther.compiler.core.KernelContracts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

/**
 * What working a tree out may end a run without a value for, read in a tree where the library's
 * operations stand as calls — the tree a reading of what a body states walks.
 *
 * <p>Asked of the owners, and never worked out again: what an operator ends a run for is
 * {@link AbortSites}', and what a kernel the library implements ends one for is
 * {@link KernelContracts}'. Where neither answers — an operation the library writes in the language,
 * whose body is not in this tree; a helper, a behavior or a function value; a construction, whose
 * invariant is its declaration's — what it ends a run for is not known, which is not that it ends
 * none ({@link Endings.NotKnown}).
 */
public final class WhatARunMayEndFor {

    private WhatARunMayEndFor() {
    }

    /** What working something out may end a run without a value for. */
    public sealed interface Endings {

        /** These reasons, and no other; none at all where it never ends one. */
        record Known(AbortSet kinds) implements Endings {

            public Known {
                Objects.requireNonNull(kinds, "the reasons a run may end for, or none");
            }
        }

        /** Something here ends a run for what nothing here says. */
        record NotKnown() implements Endings {}

        /** Whether it is known to end no run at all. */
        default boolean endsNone() {
            return this instanceof Known(AbortSet kinds) && kinds.isEmpty();
        }

        /** What this and {@code other} may end a run for, worked out both. */
        default Endings and(Endings other) {
            return this instanceof Known(AbortSet mine) && other instanceof Known(AbortSet theirs)
                    ? new Known(mine.union(theirs)) : new NotKnown();
        }
    }

    private static final Endings NONE = new Endings.Known(AbortSet.NONE);

    /**
     * What each operation of the library a kernel implements ends a run for, read off the library
     * once: the library is the same for every compilation, and which kernel an operation is is a
     * fact of the library alone.
     */
    private static final class Kernels {
        private static final Map<ValueName.Stdlib.Operation, AbortSet> ENDING = ending();

        private static Map<ValueName.Stdlib.Operation, AbortSet> ending() {
            Stdlib library = DefaultStdlib.get();
            Map<ValueName.Stdlib.Operation, AbortSet> out = new HashMap<>();
            for (ValueName.Stdlib.Operation operation : library.entries().keySet()) {
                Stdlib.Intrinsic intrinsic = library.intrinsicOf(operation);
                if (intrinsic != null) {
                    out.put(operation, KernelContracts.abortsOf(intrinsic.kernel()));
                }
            }
            return Map.copyOf(out);
        }
    }

    /** What working {@code e} out, and everything under it, may end a run without a value for. */
    public static Endings of(Core e) {
        Core node = Core.withoutStanding(e);
        if (node instanceof Core.IfConstructed attempt) {
            // The construction an attempt tests takes the other arm where it is refused, and ends
            // nothing; what it is built of is worked out first all the same.
            Endings[] out = {NONE};
            Core.forEachChild(attempt.construct(), child -> out[0] = out[0].and(of(child)));
            out[0] = out[0].and(of(attempt.then()));
            for (Core.ElseArm arm : attempt.els()) {
                out[0] = out[0].and(of(arm.body()));
            }
            return out[0];
        }
        Endings[] out = {itself(node)};
        Core.forEachChild(node, child -> {
            if (out[0] instanceof Endings.Known) {
                out[0] = out[0].and(of(child));
            }
        });
        return out[0];
    }

    /** What {@code e} itself, and none of what it is made of, may end a run for. */
    private static Endings itself(Core e) {
        Core node = Core.withoutStanding(e);
        if (node instanceof Core.Binary binary) {
            return new Endings.Known(AbortSites.ofAnOperator(binary));
        }
        if (node instanceof Core.Neg neg) {
            return new Endings.Known(AbortSites.ofANegation(neg));
        }
        if (node instanceof Core.Unreachable) {
            return new Endings.Known(AbortSet.of(AbortKind.UNREACHABLE_REACHED));
        }
        if (node instanceof Core.Call call && call.fn() instanceof Core.Reached.OfKernel kernel) {
            return new Endings.Known(KernelContracts.abortsOf(kernel.kernel()));
        }
        if (node instanceof Core.Apply || node instanceof Core.Construct) {
            return new Endings.NotKnown();
        }
        AnOperationApplied applied = AnOperationApplied.of(node);
        if (applied == null) {
            return node instanceof Core.Call ? new Endings.NotKnown() : NONE;
        }
        AbortSet ending = applied.operation() instanceof ValueName.Stdlib.Operation operation
                ? Kernels.ENDING.get(operation) : null;
        return ending != null ? new Endings.Known(ending) : new Endings.NotKnown();
    }
}
