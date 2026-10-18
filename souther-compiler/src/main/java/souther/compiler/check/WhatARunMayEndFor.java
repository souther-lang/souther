package souther.compiler.check;

import souther.compiler.abort.AbortSet;
import souther.compiler.abort.AbortSites;
import souther.compiler.core.Core;
import souther.compiler.core.KernelContracts;
import souther.compiler.types.ValueName;

import java.util.Objects;

/**
 * What working a tree out may end a run without a value for, read in a tree where the library's
 * operations stand as calls — the tree a reading of what a body states walks.
 *
 * <p>Asked of the owners, and never worked out again: what an operator ends a run for is
 * {@link AbortSites}', what a kernel ends one for is {@link KernelContracts}', and what an operation
 * of the library ends one for, a kernel or one it writes in the language, is
 * {@link LibraryEndings}'. Where none answers — a helper, a behavior or a function value; a
 * construction, whose invariant is its declaration's — what it ends a run for is not known, which is
 * not that it ends none ({@link Endings.NotKnown}).
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

    /**
     * What {@code e} itself, and none of what it is made of, may end a run for.
     *
     * <p>Exhaustive over {@link Core}, as {@link AbortSites}' own reading of a site is, so a node
     * kind added later stops the build here and not only there. Where a node's own answer is a site's
     * wherever it stands, it is {@link AbortSites}' answer. Where it is not — a call whose callee's
     * body is a root of its own, a function value, a construction whose invariant is its
     * declaration's — what working it out ends a run for is not in this tree.
     */
    private static Endings itself(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.Unreachable unreachable ->
                    new Endings.Known(AbortSites.ofAnUnreachable(unreachable));
            case Core.Binary binary -> new Endings.Known(AbortSites.ofAnOperator(binary));
            case Core.Neg neg -> new Endings.Known(AbortSites.ofANegation(neg));
            case Core.Call call -> switch (call.fn()) {
                case Core.Reached.OfKernel kernel ->
                        new Endings.Known(KernelContracts.abortsOf(kernel.kernel()));
                case Core.Emitted emitted -> new Endings.Known(AbortSites.ofAnEmittedCall(emitted));
                case Core.Reached.OfDeclaration _, Core.Reached.OfValue _,
                     Core.Reached.OfPublishedValue _ -> new Endings.NotKnown();
            };
            case Core.PreservedCall kept -> ofTheLibrary(kept);
            case Core.Apply _, Core.Construct _ -> new Endings.NotKnown();
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _, Core.Read _,
                 Core.UnitValue _, Core.MaterialisedValue _, Core.OptionNone _,
                 Core.FieldAccess _, Core.FieldProjection _, Core.If _, Core.IfConstructed _,
                 Core.LetIn _, Core.Block _, Core.ListLit _, Core.OptionSome _, Core.Tuple _,
                 Core.TupleGet _, Core.Match _, Core.Widen _ -> NONE;
        };
    }

    /** What an operation of the library a call keeps ends a run for, over every call of it
     *  ({@link LibraryEndings}). */
    private static Endings ofTheLibrary(Core.PreservedCall kept) {
        AnOperationApplied applied = AnOperationApplied.of(kept);
        return applied != null
                && applied.operation() instanceof ValueName.Stdlib.Operation operation
                ? LibraryEndings.shipped().of(operation) : new Endings.NotKnown();
    }
}
