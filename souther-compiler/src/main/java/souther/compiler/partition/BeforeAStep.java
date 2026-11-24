package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * What a run works out before it gets to a step, by one way: each part with the names it is
 * worked out in and whether every run getting there works it out.
 *
 * <p>The one account of it a reader of the step takes, so that what a proof rests on is never
 * more than the account holds. A part read in names the account keeps is read in those names; a
 * part a reader cannot read in them is not met by that reader, only got past.
 *
 * @param parts what a run works out first, in the order it does
 */
record BeforeAStep(List<Part> parts) {

    BeforeAStep {
        parts = List.copyOf(parts);
    }

    /**
     * A part of what a run works out before a step, with the names it is worked out in; with
     * none, each step in it is read with the names where the walk met it.
     *
     * @param every whether every run getting to the step works it out, and not only some
     */
    record Part(Core node, InputReads names, boolean every) {}

    /** What the way {@code first} says a run works out before the step, each part read with
     *  the names where the walk met it. */
    static BeforeAStep onTheWay(WhatARunWorksOutBeforeACount.BeforeAConstruction first) {
        Set<Core> onEveryRun = Collections.newSetFromMap(new IdentityHashMap<>());
        onEveryRun.addAll(first.onEveryRun());
        List<Part> out = new ArrayList<>();
        first.onSomeRun().forEach(part -> out.add(new Part(part, null, onEveryRun.contains(part))));
        return new BeforeAStep(out);
    }

    /**
     * What a run on one application of a function value works out before the step: what it
     * works out in each tree it goes through before it gets into the one the step stands in
     * ({@code goingIn}), and then {@code inside}, what that application works out up to the
     * step. Empty where what comes first going in is not read: what the application works out
     * is then not all a run has worked out.
     */
    static Optional<BeforeAStep> onAnApplication(
            Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction> goingIn, List<Part> inside) {
        return goingIn.map(first -> {
            List<Part> out = new ArrayList<>(onTheWay(first).parts());
            out.addAll(inside);
            return new BeforeAStep(out);
        });
    }

    /**
     * The same as a reader of what a construction asks reads it, which reads each part in the
     * names where the walk met it; empty where some part is worked out in names of its own — an
     * application's — which that reader cannot read it in. Read in other names, such a part is
     * neither what a run has met nor what a value has to get past, so the account is not handed
     * to that reader in part: it is handed whole or not at all.
     */
    Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction> asAConstructionReadsIt() {
        if (parts.stream().anyMatch(part -> part.names() != null)) {
            return Optional.empty();
        }
        return Optional.of(new WhatARunWorksOutBeforeACount.BeforeAConstruction(
                parts.stream().map(Part::node).toList(),
                parts.stream().filter(Part::every).map(Part::node).toList()));
    }
}
