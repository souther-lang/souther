package souther.compiler.check;

import souther.compiler.abort.GetsPast;
import souther.compiler.core.Core;
import souther.compiler.types.ValueName;

import java.util.Optional;
import java.util.Set;

/**
 * What a run of a row gets past, for every reader that draws classes over the rows or reads what a
 * body states of them: what {@link WhatARunMayEndFor} says a run gets past, and besides that three
 * premises, written here and nowhere else.
 *
 * <p>An {@code unreachable} states that no run reaches it (spec §unreachable). A row that reaches
 * one is the model's fault, told when the row is run, and is no row to hand anybody, so a run of a
 * row is taken to get past it. A call of a behavior is gotten past where the runs of every row of
 * the behavior are ({@link BehaviorAnswers#rowsRunsGetPast}), whatever the call hands it: the
 * behavior's own rows answer for its body. And an operation that ends a run only past what the
 * representation holds ({@link GetsPast#endsOnlyPastTheRepresentation}) is gotten past. A class is
 * drawn over the values a model tells apart, and where a {@code String} or a collection stops is
 * none of those, so that a run stops there is said once, of the operation. A construction whose
 * invariant is not shown to hold on every run that makes it is no premise anything writes, and is
 * not taken so.
 *
 * <p>What {@link WhatARunMayEndFor} says stands for every reader that asks whether a run stops,
 * and where: one that reaches an {@code unreachable} aborts, and a proof that a path completes or
 * that a body ends no run asks it and not this.
 */
public final class ARowsRun {

    private ARowsRun() {
    }

    /**
     * Where a run of a row gets past {@code e} itself, apart from the closures written at it, as
     * {@link WhatARunMayEndFor#completionApartFromTheClosuresWrittenAtIt} reads it, under the
     * premises a run of a row is taken under.
     */
    public static GetsPast completionOf(Core e, BehaviorAnswers answers) {
        Core node = Core.withoutStanding(e);
        // What every run gets past is asked first: most of a tree is, and no premise is asked of it.
        GetsPast owned = WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(node);
        if (owned instanceof GetsPast.Always) {
            return owned;
        }
        Optional<GetsPast> premised = premised(node, answers);
        if (premised.isPresent()) {
            return premised.get();
        }
        return owned.endsOnlyPastTheRepresentation() ? new GetsPast.Always() : owned;
    }

    /**
     * Whether a run of a row gets past {@code e} itself, the closures written at it read as part of
     * it ({@link WhatARunMayEndFor#itself}), under the same premises.
     */
    public static boolean getsPastWhole(Core e, BehaviorAnswers answers) {
        Core node = Core.withoutStanding(e);
        WhatARunMayEndFor.Endings whole = WhatARunMayEndFor.itself(node);
        if (whole.endsNone()) {
            return true;
        }
        Optional<GetsPast> premised = premised(node, answers);
        if (premised.isPresent()) {
            return premised.get() instanceof GetsPast.Always;
        }
        // Where what it ends a run for whole is what it ends one for apart from the closures, where
        // it answers apart from them is where it answers.
        return whole.equals(WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(node))
                && WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(node)
                        .endsOnlyPastTheRepresentation();
    }

    /**
     * Whether a run of a row gets past working out {@code e} and everything under it: each node
     * apart from the closures written at it ({@link #completionOf}), whose bodies are under it.
     */
    public static boolean getsPastBeneath(Core e, BehaviorAnswers answers) {
        return getsPastBeneathApart(e, Set.of(), answers);
    }

    /**
     * The same, apart from the expressions in {@code apart}, which are asked of someone else: the
     * elements of a list a reading takes one by one.
     */
    public static boolean getsPastBeneathApart(Core e, Set<Core> apart, BehaviorAnswers answers) {
        Core here = Core.withoutStanding(e);
        if (apart.contains(here)) {
            return true;
        }
        if (!(completionOf(here, answers) instanceof GetsPast.Always)) {
            return false;
        }
        boolean[] under = {true};
        Core.forEachChild(here, child -> under[0] &= getsPastBeneathApart(child, apart, answers));
        return under[0];
    }

    /**
     * Whether a run of a row is taken to get past {@code e} by a premise it is written under: an
     * {@code unreachable}, or a call of a behavior whose own rows get past its body. What a
     * reader saying where a run stops asks, since a stop at either is said where the premise is
     * accounted for: of the model's rows, and of the called behavior's body. Not the operations
     * that end a run only past what a representation holds, which a class is not drawn over and
     * a run still stops at.
     */
    public static boolean takenAsGotPast(Core e, BehaviorAnswers answers) {
        return premised(Core.withoutStanding(e), answers).orElse(null)
                instanceof GetsPast.Always;
    }

    /** What a premise of a row's run says of {@code node}; none where no premise speaks of it. */
    private static Optional<GetsPast> premised(Core node, BehaviorAnswers answers) {
        if (Core.withoutStanding(node) instanceof Core.Unreachable) {
            return Optional.of(new GetsPast.Always());
        }
        if (AnOperationApplied.of(node) instanceof AnOperationApplied applied
                && applied.operation() instanceof ValueName.Behavior behavior) {
            return Optional.of(answers.rowsRunsGetPast(behavior) ? new GetsPast.Always()
                    : new GetsPast.NotKnown());
        }
        return Optional.empty();
    }
}
