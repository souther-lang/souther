package souther.compiler.check;

import souther.compiler.abort.AbortSet;
import souther.compiler.abort.AbortSites;
import souther.compiler.abort.GetsPast;
import souther.compiler.core.Core;
import souther.compiler.core.KernelContracts;
import souther.compiler.semantics.Accumulation;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.Objects;
import java.util.Set;
import java.util.function.Consumer;

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
            Endings[] out = {NONE};
            forEachWorkedOut(attempt, part -> out[0] = out[0].and(of(part)));
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
     * What working out {@code attempt} is made of, each part handed to {@code visit}: what the
     * construction it tests is built of, then its arms.
     *
     * <p>Not the construction itself. It takes the other arm where it is refused, and ends
     * nothing; what it is built of is worked out first all the same. The one place that is said,
     * for every reader that walks a tree for what working it out may end a run for.
     */
    public static void forEachWorkedOut(Core.IfConstructed attempt, Consumer<Core> visit) {
        Core.forEachChild(attempt.construct(), visit);
        visit.accept(attempt.then());
        for (Core.ElseArm arm : attempt.els()) {
            visit.accept(arm.body());
        }
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
    public static Endings itself(Core e) {
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

    /**
     * What {@code e} itself may end a run for, as {@link #itself} says, but for a call of an
     * operation of the library every function it is handed at which is a closure written at the
     * call: what the operation ends a run for apart from those
     * ({@link LibraryEndings#apartFromWhatItIsHanded}). For a reader that asks the body of each
     * such closure itself, as part of the call. A function handed some other way — a name, a
     * value worked out elsewhere — has a body in no tree that reader walks, and the call is
     * answered whole.
     */
    public static Endings itselfApartFromTheClosuresWrittenAtIt(Core e) {
        if (!(Core.withoutStanding(e) instanceof Core.PreservedCall kept)
                || !closuresWrittenAt(kept)) {
            return itself(e);
        }
        AnOperationApplied applied = AnOperationApplied.of(kept);
        return applied != null && applied.operation() instanceof ValueName.Stdlib.Operation operation
                ? LibraryEndings.shipped().apartFromWhatItIsHanded(operation)
                : new Endings.NotKnown();
    }

    /**
     * Whether working {@code e} out, and everything under it, ends no run: a call handed a
     * closure written at it is asked apart from the closure, whose body is under it.
     */
    public static boolean endsNoneBeneath(Core e) {
        return endsNoneBeneathApart(e, Set.of());
    }

    /**
     * The same, apart from the expressions in {@code apart}, which are asked of someone else:
     * the elements of a list a reading takes one by one.
     */
    public static boolean endsNoneBeneathApart(Core e, Set<Core> apart) {
        Core here = Core.withoutStanding(e);
        if (apart.contains(here)) {
            return true;
        }
        if (!itselfApartFromTheClosuresWrittenAtIt(here).endsNone()) {
            return false;
        }
        boolean[] under = {true};
        Core.forEachChild(here, child -> under[0] &= endsNoneBeneathApart(child, apart));
        return under[0];
    }

    /**
     * Where {@code e} itself answers ({@link GetsPast}), apart from the closures written at it
     * as {@link #itselfApartFromTheClosuresWrittenAtIt} reads it, each from the owner of what it
     * is: an operator's from {@link AbortSites}, a kernel's from {@link KernelContracts}, and an
     * operation of the library's from {@link LibraryEndings}. Its operands are counted in the order
     * they are written, a binary's left one first.
     */
    public static GetsPast completionApartFromTheClosuresWrittenAtIt(Core e) {
        if (itselfApartFromTheClosuresWrittenAtIt(e).endsNone()) {
            return new GetsPast.Always();
        }
        GetsPast total = whereTheTotalFits(e);
        if (total != null) {
            return total;
        }
        return switch (Core.withoutStanding(e)) {
            case Core.Binary binary -> AbortSites.completionOfAnOperator(binary.op(), binary.type());
            case Core.Call call when call.fn() instanceof Core.Reached.OfKernel kernel ->
                    KernelContracts.completionOf(kernel.kernel());
            case Core.PreservedCall kept when closuresWrittenAt(kept) -> {
                AnOperationApplied applied = AnOperationApplied.of(kept);
                yield applied != null
                        && applied.operation() instanceof ValueName.Stdlib.Operation operation
                        ? LibraryEndings.shipped().completionApartFromWhatItIsHanded(operation)
                        : new GetsPast.NotKnown();
            }
            default -> new GetsPast.NotKnown();
        };
    }

    /**
     * Where a call adding up the {@code Int}s of a list answers, or null where {@code e} is no
     * such call: what it accumulates is the operation's own account ({@link Accumulations}), from
     * nought by adding, and the total it answers is an {@code Int}.
     */
    private static GetsPast whereTheTotalFits(Core e) {
        if (!(Core.withoutStanding(e) instanceof Core.PreservedCall kept)
                || kept.type() != Type.INT) {
            return null;
        }
        Accumulations.Accumulating accumulating = Accumulations.accumulating(kept);
        if (accumulating == null || !accumulating.what().equals(new Accumulation(
                Accumulation.Identity.ZERO, Accumulation.Combine.ADD))) {
            return null;
        }
        for (int at = 0; at < kept.args().size(); at++) {
            if (kept.args().get(at) == accumulating.container()) {
                return new GetsPast.WhereTheTotalFits(at);
            }
        }
        return null;
    }

    /** Whether every function {@code kept} is handed is a closure written at the call. */
    private static boolean closuresWrittenAt(Core.PreservedCall kept) {
        return kept.args().stream().allMatch(arg -> !(arg.type() instanceof Type.FnOf)
                || Core.withoutStanding(arg) instanceof Core.Block);
    }

    /** What an operation of the library a call keeps ends a run for, over every call of it
     *  ({@link LibraryEndings}). */
    private static Endings ofTheLibrary(Core.PreservedCall kept) {
        AnOperationApplied applied = AnOperationApplied.of(kept);
        return applied == null ? new Endings.NotKnown() : ofAnOperation(applied.operation());
    }

    /** What applying {@code operation} itself, and none of what it is handed, may end a run for:
     *  an operation of the library's as {@link LibraryEndings} says, and not known of any other. */
    public static Endings ofAnOperation(ValueName operation) {
        return operation instanceof ValueName.Stdlib.Operation ofTheLibrary
                ? LibraryEndings.shipped().of(ofTheLibrary) : new Endings.NotKnown();
    }
}
