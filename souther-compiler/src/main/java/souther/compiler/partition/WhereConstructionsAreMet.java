package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Where the walk of a body met each construction in it: what stood on the way to it, and the
 * names as they stand there — and where it met each function value and each call handed one by a
 * name, which is where a run goes into the body of the function value.
 *
 * <p>What the walk says and nobody else, as {@link WaysToNodes} is for the parts of a condition:
 * it is the walk that meets the arm of a choice under what the arm proves, and the right of an
 * {@code &&} under the left coming out true, so a construction on an arm is met under the arm's
 * condition. A reader that asks whether a run gets to a construction, and which, asks for its way
 * here and not a second account of where evaluation goes.
 *
 * <p>Of the behavior's own body and of the templates of the values it builds: a helper's body read
 * at a call is read under ways that are not one run of this body.
 *
 * <p>Complete once the walk is, and shared by every reading of the body it is made for — and so
 * where what a run works out going in at such a call or build is kept, once for each, for every
 * rule a run goes on there to.
 */
final class WhereConstructionsAreMet {

    /** Where the walk met a construction: the way to it, the names there, and the applications
     *  of the closures it stands inside, which say what of the way to it is met on each. */
    record Met(List<OnTheWay> way, InputReads reads, ClosureApplications applying) {

        Met {
            way = List.copyOf(way);
        }
    }

    private final Map<Core.Construct, List<Met>> met = new IdentityHashMap<>();
    private final Map<Core.Block, List<List<OnTheWay>>> made = new IdentityHashMap<>();
    private final Map<Core, List<List<OnTheWay>>> handing = new IdentityHashMap<>();
    private final Map<Core, Optional<List<Core.Construct>>> metBeforeGoingIn =
            new IdentityHashMap<>();
    private final Map<Core, Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction>>
            workedOutGoingIn = new IdentityHashMap<>();

    /** That the walk met {@code made} on {@code way}, with the names as {@code reads} has them,
     *  inside {@code applying}. */
    void met(Core.Construct made, List<OnTheWay> way, InputReads reads,
             ClosureApplications applying) {
        met.computeIfAbsent(made, _ -> new ArrayList<>(1)).add(new Met(way, reads, applying));
    }

    /**
     * Where the walk met {@code made}, where it met it once: empty where it never did, or did more
     * than once, as a construction in a closure read on each application is, which is no one way.
     */
    Optional<Met> at(Core.Construct made) {
        return once(met.get(made));
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

    /**
     * Every construction a run may work out before it goes on into another body at {@code at}, a
     * node of {@code root}'s tree ({@link WhatARunWorksOutBeforeACount#constructionsARunMayMeetBefore}):
     * worked out once for each such node, however many rules a run goes on there to.
     */
    Optional<List<Core.Construct>> metBeforeGoingIn(Core root, Core at) {
        return metBeforeGoingIn.computeIfAbsent(at, _ ->
                WhatARunWorksOutBeforeACount.constructionsARunMayMeetBefore(root, at));
    }

    /** What a run works out going into another body at {@code at}, a node of {@code root}'s
     *  tree ({@link WhatARunWorksOutBeforeACount#workedOutGoingIn}), once for each such node. */
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
