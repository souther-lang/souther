package souther.compiler.partition;

import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Supplier;

/**
 * Where the walk of a body met each step a run may stop at: what stood on the way to it, the
 * names as they stand there, and the ways a run gets into the tree it stands in — and where it
 * met each function value and each call handed one by a name, which is where a run goes into the
 * body of the function value.
 *
 * <p>A step a run may stop at is a node whose own working out may end a run
 * ({@link WhatARunMayEndFor#itselfApartFromTheClosuresWrittenAtIt}), or a construction, whose
 * invariant is its declaration's to say. Not a function value, whose body runs where it is
 * applied and holds its own steps; not an application of one or a build of a value, whose body or
 * template the walk goes through and whose steps are met there; and not the construction an
 * attempt tests, which takes the other arm where it is refused. Met whether or not a comparison
 * comes after it, and whether or not what it works out is read: a run that stops there stops
 * whatever follows.
 *
 * <p>What the walk says and nobody else, as {@link WaysToNodes} is for the parts of a condition:
 * it is the walk that meets the arm of a choice under what the arm proves, and the right of an
 * {@code &&} under the left coming out true, so a step on an arm is met under the arm's
 * condition. A reader that asks whether a run gets to a step, and which, asks for its way here and
 * not a second account of where evaluation goes.
 *
 * <p>Of the behavior's own body and of the templates of the values it builds: a helper's body read
 * at a call is read under ways that are not one run of this body.
 *
 * <p>Complete once the walk is, and shared by every reading of the body it is made for — and so
 * where what a run works out going in at such a call or build is kept, once for each, for every
 * step a run goes on there to.
 */
final class WhereARunMayStop {

    /**
     * Where the walk met a step a run may stop at: the way to it, the names there, the
     * applications of the closures it stands inside, which say what of the way to it is met on
     * each, the ways a run gets into the tree it stands in, worked out where they are asked, and
     * that tree.
     */
    record Met(List<OnTheWay> way, InputReads reads, ClosureApplications applying,
               Supplier<WaysToASite> ways, Core tree) {

        Met {
            way = List.copyOf(way);
        }
    }

    /** Each step by the node it is, and the steps in the order the walk first met them. */
    private final Map<Core, List<Met>> met = new IdentityHashMap<>();
    private final List<Core> inOrder = new ArrayList<>();
    private final Set<Core> placed = Collections.newSetFromMap(new IdentityHashMap<>());
    private final Set<Core> tested = Collections.newSetFromMap(new IdentityHashMap<>());
    private final Map<Core.Block, List<List<OnTheWay>>> made = new IdentityHashMap<>();
    private final Map<Core, List<List<OnTheWay>>> handing = new IdentityHashMap<>();
    private final Map<Core, Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction>>
            workedOutGoingIn = new IdentityHashMap<>();

    /** Whether {@code e} is a step a run may stop at, as this class says it. */
    static boolean aStepARunMayStopAt(Core e) {
        if (Core.withoutStanding(e) != e) {
            return false;
        }
        return switch (e) {
            case Core.Construct _ -> true;
            case Core.Apply _, Core.MaterialisedValue _, Core.Block _ -> false;
            default -> !WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(e).endsNone();
        };
    }

    /** That {@code made} is the construction an attempt tests, which is no step a run stops at.
     *  Said before the walk goes into it. */
    void tested(Core made) {
        tested.add(Core.withoutStanding(made));
    }

    /** That the walk met {@code step}, where it is a step a run may stop at, in {@code tree} on
     *  {@code way}, with the names as {@code reads} has them, inside {@code applying}, a run
     *  getting into its tree by {@code ways}. */
    void met(Core step, List<OnTheWay> way, InputReads reads, ClosureApplications applying,
             Supplier<WaysToASite> ways, Core tree) {
        if (!aStepARunMayStopAt(step) || tested.contains(step)) {
            return;
        }
        met.computeIfAbsent(step, _ -> new ArrayList<>(1))
                .add(new Met(way, reads, applying, new Pullback.Once<>(ways), tree));
    }

    /** That the walk has gone through everything under {@code e}: where it is a step met, it is
     *  put in order after what it is worked out of. */
    void walkedPast(Core e) {
        if (met.containsKey(e) && placed.add(e)) {
            inOrder.add(e);
        }
    }

    /** Every step met, each once, in the order a run takes them: what a step is worked out of
     *  before it. */
    List<Core> steps() {
        return Collections.unmodifiableList(inOrder);
    }

    /** Every place the walk met {@code step}; none where it never did. */
    List<Met> everyPlace(Core step) {
        List<Met> found = met.get(step);
        return found == null ? List.of() : Collections.unmodifiableList(found);
    }

    /**
     * Where the walk met {@code step}, where it met it once: empty where it never did, or did more
     * than once, as a step in a closure read on each application is, which is no one way.
     */
    Optional<Met> at(Core step) {
        return once(met.get(step));
    }

    /** That the walk met the function value {@code closure} on {@code way}. */
    void made(Core.Block closure, List<OnTheWay> way) {
        made.computeIfAbsent(closure, _ -> new ArrayList<>(1)).add(List.copyOf(way));
    }

    /** The way the walk met {@code closure} on, where it met it once. */
    Optional<List<OnTheWay>> madeOn(Core.Block closure) {
        return once(made.get(closure));
    }

    /** That the walk met {@code call}, a call handed a function value by a name, on {@code way}:
     *  where a run goes into that function value's body, if the call applies it. */
    void handing(Core call, List<OnTheWay> way) {
        handing.computeIfAbsent(call, _ -> new ArrayList<>(1)).add(List.copyOf(way));
    }

    /** The way the walk met {@code call} on, a call handed a function value by a name, where it
     *  met it once. */
    Optional<List<OnTheWay>> handingOn(Core call) {
        return once(handing.get(call));
    }

    /** What a run works out going into another body at {@code at}, a node of {@code root}'s
     *  tree ({@link WhatARunWorksOutBeforeACount#workedOutGoingIn}), once for each such node,
     *  however many steps a run goes on there to. */
    Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction> workedOutGoingIn(Core root,
                                                                               Core at) {
        return workedOutGoingIn.computeIfAbsent(at, _ ->
                WhatARunWorksOutBeforeACount.workedOutGoingIn(root, at));
    }

    private static <T> Optional<T> once(List<T> found) {
        return (found == null || found.size() != 1) ? Optional.empty()
                : Optional.of(found.getFirst());
    }
}
