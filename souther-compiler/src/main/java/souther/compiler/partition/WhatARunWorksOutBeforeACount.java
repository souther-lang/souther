package souther.compiler.partition;

import souther.compiler.check.ClosureUses;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.core.WhatABodyReads;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Quantity;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Supplier;

/**
 * Whether every row a count is read over gets through what a run works out up to the comparison
 * reading it, the comparison included, as the witness of the count did.
 *
 * <p>The rows are the witness's two elements over again, so many of each, with everything else the
 * witness holds. What the run works out is everything before the comparison — the value of each
 * {@code let} it is under, each operand and condition evaluated before the part it is in — and the
 * comparison itself, operands and operator alike: a count written inline is worked out inside the
 * comparison, and so is anything beside it there. Each part of that is one of four things.
 *
 * <p>A part that reads nothing of the container is worked out on what the witness holds, and comes
 * out as it did there. A name read works nothing out. The walk the count was read off applies a
 * step to every element, handing it the element alone, with nothing carried from one application
 * to the next and nothing of the container read inside it: each application is of an element the
 * witness held, on what the witness held besides, and comes out as it did there, and what the walk
 * keeps is the count, never more than the container holds ({@link Quantity.HowManyMeet}). Which
 * call that is, is the reading's to say, and it says so where it reads the count
 * ({@link Pullback.OnTheInput#readOff}): a count it names no call for is read off nothing here,
 * and nothing is shown of it. Anything else reading the container is worked out on a container
 * the witness never held, and is let through only where what it is ends no run on its own
 * ({@link WhatARunMayEndFor#itself}) and every part of it is one of the four in turn — a size taken
 * of the container, the comparison of two numbers. A fold, a lookup, a helper walking the
 * container, a walk that keeps a number of elements other than the count, is none of them.
 *
 * <p>Of the tree the analysis reads, where the language's operations stand as the calls they are.
 */
final class WhatARunWorksOutBeforeACount {

    private WhatARunWorksOutBeforeACount() {}

    /**
     * {@code witnesses}, kept for a count only where every row it is read over gets through what a
     * run works out up to {@code comparison}, a node of {@code root}'s tree; none where
     * {@code comparison} is not in it, or stands in a closure, whose applications are not the one
     * run a witness is of.
     *
     * <p>Worked out where a count is first asked about, and once for each count: every comparison
     * of a body is read with this beside it, and few of them read a count.
     *
     * @param reads      the names as they stand at the comparison
     * @param readOff    the call each count the reading of the comparison made was read off
     *                   ({@link Pullback.OnTheInput#readOff}), asked where a count first is
     * @param parameters the binding each parameter of the behavior is read on, by its name
     */
    static ComparisonWitnesses.AtAComparison past(Core root, Core comparison, InputReads reads,
                                      Supplier<Map<Quantity.HowManyMeet, Core>> readOff,
                                      Map<BindingId, String> parameters,
                                      ComparisonWitnesses.AtAComparison witnesses) {
        Map<Quantity.CountedOverAContainer, Boolean> getsThrough = new HashMap<>();
        List<Optional<List<Core>>> worked = new ArrayList<>(1);
        return new ComparisonWitnesses.AtAComparison() {
            @Override
            public CountWitnesses.Sought of(Quantity.CountedOverAContainer count) {
                if (root == null) {
                    return CountWitnesses.Sought.NOTHING;
                }
                if (worked.isEmpty()) {
                    worked.add(Optional.ofNullable(workedOutUpTo(root, comparison, false)));
                }
                boolean through = worked.getFirst().isPresent()
                        && getsThrough.computeIfAbsent(count, asked -> getsThrough(
                                worked.getFirst().get(), asked,
                                asked instanceof Quantity.HowManyMeet meet
                                        ? readOff.get().get(meet) : null,
                                root, reads, parameters));
                return through ? witnesses.of(count) : CountWitnesses.Sought.NOTHING;
            }

            /** A row a run of which goes through the comparison asks nothing of what the run
             *  works out before it: the run is what is watched. */
            @Override
            public ReachWitnesses.Sought reached(List<TakenConstraint> conditions) {
                return witnesses.reached(conditions);
            }

            @Override
            public BehaviorInputs.SameValue sameValue() {
                return witnesses.sameValue();
            }
        };
    }

    /**
     * Whether every one of {@code parts} is let through for {@code count}, a count of elements
     * that meet a statement read off {@code counted} — never where the reading names no call it was
     * read off — or a count of different values, which is read off no one call but a chain of
     * them over the container: each part reading the container is then let through where nothing
     * under it, the closures written at it included, ends a run, whatever the container holds.
     */
    private static boolean getsThrough(List<Core> parts, Quantity.CountedOverAContainer count,
                                       Core counted, Core root, InputReads reads,
                                       Map<BindingId, String> parameters) {
        if ((counted == null && count instanceof Quantity.HowManyMeet)
                || !(count.container() instanceof DecisionSubject.AnInput(TermPath container,
                        var _))) {
            return false;
        }
        BindingId parameter = parameterOf(container, parameters);
        if (parameter == null) {
            return false;
        }
        Set<BindingId> ofTheContainer = WhatABodyReads.namesMadeOf(root, Set.of(parameter));
        if (counted == null) {
            return parts.stream().noneMatch(part -> WhatABodyReads.anyOf(part, ofTheContainer)
                    && !WhatARunMayEndFor.endsNoneBeneath(part));
        }
        Within asked = new Within(parameter, ofTheContainer, reads,
                Core.withoutStanding(counted));
        return parts.stream().allMatch(asked::letsThrough);
    }

    /** The binding of the parameter {@code container} is under, or null where none is. */
    private static BindingId parameterOf(TermPath container, Map<BindingId, String> parameters) {
        for (Map.Entry<BindingId, String> each : parameters.entrySet()) {
            if (each.getValue().equals(container.head())) {
                return each.getKey();
            }
        }
        return null;
    }

    /**
     * What a part is judged against, for a count of the elements of the container on
     * {@code parameter}.
     *
     * @param parameter      the binding of the parameter the container is under
     * @param ofTheContainer that binding, and every name the body binds to a value reading it
     * @param reads          the names as they stand at the comparison
     * @param counted        the call the count was read off, as the reading names it
     */
    private record Within(BindingId parameter, Set<BindingId> ofTheContainer, InputReads reads,
                          Core counted) {

        /** Whether {@code e} is one of the four things a part may be. */
        boolean letsThrough(Core e) {
            if (!WhatABodyReads.anyOf(e, ofTheContainer)) {
                return true;
            }
            Core bare = Core.withoutStanding(e);
            if (bare instanceof Core.Read) {
                return true;
            }
            if (bare == counted) {
                return aWalkOfItsElements(bare)
                        && argumentsBesideTheStep(bare).stream().allMatch(this::letsThrough);
            }
            if (bare instanceof Core.Block) {
                return false;
            }
            for (Core each : Core.subexpressionsAt(bare)) {
                if (!WhatARunMayEndFor.itself(each).endsNone()) {
                    return false;
                }
            }
            boolean[] every = {true};
            Core.forEachChild(bare, child -> every[0] = every[0] && letsThrough(child));
            return every[0];
        }

        /**
         * Whether {@code e} is a call applying one closure, which it alone applies, to every
         * element of the container as it is, handing it the element and nothing an application
         * before it made, and reading nothing of the container inside it.
         */
        private boolean aWalkOfItsElements(Core e) {
            Core.Block step = stepOf(e);
            ClosureUses uses = step == null ? null : reads.usesOf(step);
            if (uses == null || uses.theOnlyApplication().isEmpty()
                    || WhatABodyReads.anyOf(step.body(), ofTheContainer)) {
                return false;
            }
            ClosureUses.Application applied = uses.theOnlyApplication().get();
            return applied.applied() == HowAClosureIsApplied.TO_EVERY_ELEMENT
                    && applied.call() == e
                    && applied.madeByTheApplicationsBefore().isEmpty()
                    && offTheParameter(applied.container(), parameter);
        }

        /** The one closure the call {@code e} is handed, or null where it is no call or is
         *  handed none or several. */
        private static Core.Block stepOf(Core e) {
            Core.Block step = null;
            for (Core arg : argumentsOf(e)) {
                if (Core.withoutStanding(arg) instanceof Core.Block block) {
                    if (step != null) {
                        return null;
                    }
                    step = block;
                }
            }
            return step;
        }

        /** What the call {@code e} is handed beside its closure. */
        private static List<Core> argumentsBesideTheStep(Core e) {
            return argumentsOf(e).stream()
                    .filter(arg -> !(Core.withoutStanding(arg) instanceof Core.Block))
                    .toList();
        }

        /** What the call {@code e} is handed, or nothing where it is no call. */
        private static List<Core> argumentsOf(Core e) {
            return switch (Core.withoutStanding(e)) {
                case Core.Call applying -> applying.args();
                case Core.PreservedCall applying -> applying.args();
                default -> List.of();
            };
        }
    }

    /** Whether {@code e} is the parameter on {@code parameter}, or a field of it read down some
     *  path: a value the row holds, which reading works nothing out. */
    private static boolean offTheParameter(Core e, BindingId parameter) {
        return switch (Core.withoutStanding(e)) {
            case Core.Read read -> read.binding().equals(parameter);
            case Core.FieldAccess access -> offTheParameter(access.target(), parameter);
            case Core.FieldProjection projection -> offTheParameter(projection.base(), parameter);
            default -> false;
        };
    }

    /**
     * What a run works out up to {@code comparison}, a node of {@code root}'s tree, in the order
     * it does, the comparison last — or null where it is not in the tree, or stands in a closure
     * no call it is handed to applies.
     *
     * <p>The value of every {@code let} whose body it is in, and every part of each node on the
     * way that runs before the part it is in: an operand before it, a condition deciding the
     * branch it is in. A part that runs only on some runs is counted as running, which asks more
     * of the way and never less — or left out, where {@code onlyWhatAlwaysRuns}, which says less
     * of the way and never more.
     *
     * <p>Where the way goes into a closure a call is handed, the call whole: whatever it is
     * handed beside the closure is worked out before it applies the closure, and every
     * application of the closure before the one the comparison is reached in runs the closure's
     * body whole, the parts after the comparison as well, as the call's own working out between
     * applications does. Read whole the call says more than any one application runs, which asks
     * more of the way and never less.
     */
    private static List<Core> workedOutUpTo(Core root, Core comparison,
                                            boolean onlyWhatAlwaysRuns) {
        return workedOutUpTo(root, comparison, onlyWhatAlwaysRuns, false);
    }

    /**
     * The same, a function value on the way filed as well where {@code withFunctionValues}: a
     * reader asking what may be applied before the comparison asks it of those too, since a
     * function value a run makes on the way may be applied before it.
     */
    private static List<Core> workedOutUpTo(Core root, Core comparison,
                                            boolean onlyWhatAlwaysRuns,
                                            boolean withFunctionValues) {
        List<Core> way = wayDownTo(root, comparison);
        if (way == null) {
            return null;
        }
        List<Core> out = new ArrayList<>();
        for (int i = 0; i + 1 < way.size(); i++) {
            Core child = way.get(i + 1);
            switch (way.get(i)) {
                case Core.Block block -> {
                    Core applying = i == 0 ? null : way.get(i - 1);
                    if (applying == null || Within.argumentsOf(applying).stream()
                            .noneMatch(arg -> Core.withoutStanding(arg) == block)) {
                        return null;
                    }
                    out.add(applying);
                    out.add(comparison);
                    return out;
                }
                // Standing as a wider type works nothing out of its own.
                case Core.Widen _ -> { }
                case Core.LetIn let -> {
                    if (child == let.body()) {
                        workedOut(out, let.value(), withFunctionValues);
                    }
                }
                // What an attempt works out before it is built is what the construction is built
                // of, which the way meets one step down, at the construction.
                case Core.IfConstructed attempt when child == attempt.construct() -> { }
                case Core node -> {
                    for (Evaluated.Step step : Evaluated.inOrder(node)) {
                        if (step.expression() == child) {
                            break;
                        }
                        if (!onlyWhatAlwaysRuns || step instanceof Evaluated.Step.Always) {
                            workedOut(out, step.expression(), withFunctionValues);
                        }
                    }
                }
            }
        }
        out.add(comparison);
        return out;
    }

    /**
     * Every construction a run on the way to {@code comparison}, a node of {@code root}'s tree,
     * may work out before it, each once, in the order the parts holding them are worked out — or
     * empty where what a run works out before it is not read ({@link #workedOutUpTo}): it is not in
     * the tree, or stands in a function value that is not handed to the call applying it, whose
     * applications may come anywhere. Empty is that it is not read, and never that there is none:
     * a reader then asks of every construction that may come first
     * ({@link #everyConstructionIn}).
     *
     * <p>Every construction under a part a run may work out first ({@link #workedOutUpTo}, a part
     * that runs only on some runs counted as running), on whichever arm of it, and under a function
     * value made on the way, which may be applied before the comparison. Gathered by where it is
     * written and not by whether every run gets to it, so that one only some runs get to is among
     * them, and whether a run gets to it is asked of each afterwards
     * ({@link #workedOutBeforeAConstruction}).
     *
     * <p>Not the construction an attempt tests, which no run gets past or stops at: whether it is
     * built is what the attempt decides ({@link Evaluated#inOrder}). What it is built of is among
     * them. And nothing under the comparison, which is the relation's own working out.
     */
    static Optional<List<Core.Construct>> constructionsARunMayMeetBefore(Core root,
                                                                       Core comparison) {
        List<Core> parts = root == null ? null : workedOutUpTo(root, comparison, false, true);
        if (parts == null) {
            return Optional.empty();
        }
        Set<Core> met = Collections.newSetFromMap(new IdentityHashMap<>());
        List<Core.Construct> out = new ArrayList<>();
        for (Core part : parts.subList(0, parts.size() - 1)) {
            constructionsUnder(part, comparison, null, met, out);
        }
        return Optional.of(List.copyOf(out));
    }

    /**
     * Every construction written in {@code trees} but under {@code comparison}, each once, in the
     * order the trees are walked: what a run may work out before a comparison whose way is not
     * read, every one of which may be worked out first, and none of which a run is shown to get
     * to. Not the construction an attempt tests, as above.
     */
    static List<Core.Construct> everyConstructionIn(List<Core> trees, Core comparison) {
        Set<Core> met = Collections.newSetFromMap(new IdentityHashMap<>());
        List<Core.Construct> out = new ArrayList<>();
        for (Core tree : trees) {
            constructionsUnder(tree, comparison, null, met, out);
        }
        return List.copyOf(out);
    }

    /** Every construction under {@code e}, each once: what a call is handed, all of which is
     *  worked out before the body it goes into runs. Not the construction an attempt tests, as
     *  above. */
    static List<Core.Construct> everyConstructionUnder(Core e) {
        Set<Core> met = Collections.newSetFromMap(new IdentityHashMap<>());
        List<Core.Construct> out = new ArrayList<>();
        constructionsUnder(e, null, null, met, out);
        return List.copyOf(out);
    }

    /**
     * The function value on the way down from {@code root} to {@code node} that no call it is
     * handed to applies ({@link #workedOutUpTo}), with the node it stands under, the outermost
     * where there are several — or null where there is none, or {@code node} is not in the tree.
     */
    static NotHanded notHandedOnTheWay(Core root, Core node) {
        List<Core> way = root == null ? null : wayDownTo(root, node);
        if (way == null) {
            return null;
        }
        for (int i = 0; i < way.size(); i++) {
            switch (way.get(i)) {
                case Core.Block block -> {
                    Core above = i == 0 ? null : way.get(i - 1);
                    if (above == null || Within.argumentsOf(above).stream()
                            .noneMatch(arg -> Core.withoutStanding(arg) == block)) {
                        return new NotHanded(block, above);
                    }
                }
                // A value standing as a wider type is a step of the way of its own, and the
                // function value it holds is met one step down.
                case Core.Widen _ -> { }
                default -> { }
            }
        }
        return null;
    }

    /** A function value no call it is handed to applies, and what it stands under: a
     *  {@code let} binding it to a name, or anything else that holds it. */
    record NotHanded(Core.Block closure, Core above) {}

    /**
     * Whether the way down from {@code from} to {@code node} goes into the body of a function
     * value, where what a run meets is met on each application and is not on the way the walk
     * carries alone: true as well where {@code node} is not under {@code from}.
     */
    static boolean goesIntoAFunctionValue(Core from, Core node) {
        List<Core> way = wayDownTo(from, node);
        if (way == null) {
            return true;
        }
        for (Core each : way.subList(0, way.size() - 1)) {
            switch (each) {
                case Core.Block _ -> {
                    return true;
                }
                // A value standing as a wider type is a step of the way of its own, and the
                // function value it holds is met one step down.
                case Core.Widen _ -> { }
                default -> { }
            }
        }
        return false;
    }

    /**
     * What a run works out going into another body at {@code at}, a node of {@code root}'s tree:
     * everything it works out before {@code at} ({@link #workedOutUpTo}), and everything
     * {@code at} is handed but a function value, which a call works out before it applies the
     * function it is handed ({@link Evaluated#inOrder}); the body of such a function runs where it
     * is applied and is none of it. Empty where the way to {@code at} is not read.
     */
    static Optional<BeforeAConstruction> workedOutGoingIn(Core root, Core at) {
        List<Core> some = root == null ? null : workedOutUpTo(root, at, false);
        List<Core> every = root == null ? null : workedOutUpTo(root, at, true);
        if (some == null || every == null) {
            return Optional.empty();
        }
        List<Core> onSomeRun = new ArrayList<>(some.subList(0, some.size() - 1));
        List<Core> onEveryRun = new ArrayList<>(every.subList(0, every.size() - 1));
        for (Evaluated.Step step : Evaluated.inOrder(at)) {
            workedOut(onSomeRun, step.expression());
            if (step instanceof Evaluated.Step.Always) {
                workedOut(onEveryRun, step.expression());
            }
        }
        return Optional.of(new BeforeAConstruction(onSomeRun, onEveryRun));
    }

    /**
     * What a run works out before {@code made}, a construction in what {@code at}, a node of
     * {@code root}'s tree where a run goes into another body, is handed: what the run works out
     * before {@code at}, and then, down from {@code at}, as {@link #workedOutBeforeAConstruction}
     * reads it — every run that works {@code at} out works what it is handed out before going in,
     * and a run gets to {@code made} on the runs the conditions on the way to it say. Empty where
     * a function value stands above {@code made}, whose body runs where it is applied, or the way
     * is not read.
     */
    static Optional<BeforeAConstruction> workedOutBeforeEntering(Core root, Core at,
                                                                Core.Construct made) {
        List<Core> toIt = wayDownTo(at, made);
        if (root == null || toIt == null || toIt.size() < 2) {
            return Optional.empty();
        }
        for (int i = 0; i + 1 < toIt.size(); i++) {
            if (Evaluated.makesAFunction(toIt.get(i))
                    || !entersOnSomeRun(toIt.get(i), toIt.get(i + 1), made)) {
                return Optional.empty();
            }
        }
        List<Core> someUpTo = workedOutUpTo(root, at, false);
        List<Core> everyUpTo = workedOutUpTo(root, at, true);
        List<Core> someIn = workedOutUpTo(at, made, false);
        List<Core> everyIn = workedOutUpTo(at, made, true);
        if (someUpTo == null || everyUpTo == null || someIn == null || everyIn == null) {
            return Optional.empty();
        }
        List<Core> ofIt = Evaluated.inOrder(made).stream().map(Evaluated.Step::expression)
                .toList();
        List<Core> onSomeRun = new ArrayList<>(someUpTo.subList(0, someUpTo.size() - 1));
        onSomeRun.addAll(someIn.subList(0, someIn.size() - 1));
        onSomeRun.addAll(ofIt);
        List<Core> onEveryRun = new ArrayList<>(everyUpTo.subList(0, everyUpTo.size() - 1));
        onEveryRun.addAll(everyIn.subList(0, everyIn.size() - 1));
        onEveryRun.addAll(ofIt);
        return Optional.of(new BeforeAConstruction(onSomeRun, onEveryRun));
    }

    /** Every construction under {@code e} but {@code tested}, the construction the attempt above
     *  it tests, and nothing under {@code apart}, into {@code out}, each once. */
    private static void constructionsUnder(Core e, Core apart, Core tested, Set<Core> met,
                                           List<Core.Construct> out) {
        if (e == apart) {
            return;
        }
        if (e instanceof Core.Construct made && made != tested && met.add(made)) {
            out.add(made);
        }
        Core testing = e instanceof Core.IfConstructed attempt ? attempt.construct() : null;
        Core.forEachChild(e, child -> constructionsUnder(child, apart, testing, met, out));
    }

    /**
     * Whether nothing a run works out before {@code comparison}, a node of {@code root}'s tree,
     * ends it, whatever the input: every part counted as running on some run, the comparison
     * itself left out ({@link #workedOutUpTo}), is one {@link WhatARunMayEndFor} says ends none.
     * False where it is not in the tree, stands in a closure, or some part ends a run for what
     * nothing says ({@link WhatARunMayEndFor.Endings.NotKnown}): that is not that it ends none.
     */
    static boolean nothingBeforeItEndsARun(Core root, Core comparison) {
        List<Core> worked = root == null ? null : workedOutUpTo(root, comparison, false);
        if (worked == null) {
            return false;
        }
        for (Core part : worked.subList(0, worked.size() - 1)) {
            if (!WhatARunMayEndFor.of(part).endsNone()) {
                return false;
            }
        }
        return true;
    }

    /**
     * What a run works out before {@code made}, a construction in {@code root}'s tree, where a run
     * that takes the way to {@code comparison} and the way to {@code made} works {@code made} out
     * before the comparison unless something before it ends the run — or empty where that is not
     * shown.
     *
     * <p>Shown where the two part at a node that works {@code made}'s side out on every run
     * before it enters {@code comparison}'s — a step that always runs and comes first, or the value
     * of a {@code let} whose body the comparison is in — and every node from there down to
     * {@code made} is entered by what is above it on some run. A branch, an arm and a right operand
     * that runs only where the left comes out one way are entered on the runs their conditions
     * say, which are conditions of the way to {@code made}: a reader asking of a run getting there
     * asks it to meet them as well as the way to the comparison. Above the two parting they are the
     * comparison's way too. Not where a function value stands above {@code made}, whose body runs
     * once for each application and on arguments the way does not say. And not the construction an
     * attempt tests, which no run gets past or stops at: whether it is built is what the attempt
     * decides ({@link Evaluated#inOrder}).
     *
     * <p>What it works out first is told twice ({@link BeforeAConstruction}).
     */
    static Optional<BeforeAConstruction> workedOutBeforeAConstruction(Core root, Core comparison,
                                                                      Core.Construct made) {
        List<Core> toIt = root == null ? null : wayDownTo(root, made);
        List<Core> toTheComparison = root == null ? null : wayDownTo(root, comparison);
        if (toIt == null || toTheComparison == null) {
            return Optional.empty();
        }
        int parting = 0;
        while (parting + 1 < toIt.size() && parting + 1 < toTheComparison.size()
                && toIt.get(parting + 1) == toTheComparison.get(parting + 1)) {
            parting++;
        }
        if (parting + 1 >= toIt.size() || parting + 1 >= toTheComparison.size()) {
            return Optional.empty();
        }
        for (Core above : toIt.subList(0, parting + 1)) {
            if (Evaluated.makesAFunction(above)) {
                return Optional.empty();
            }
        }
        if (!firstOnEveryRun(toIt.get(parting), toIt.get(parting + 1),
                toTheComparison.get(parting + 1), made)) {
            return Optional.empty();
        }
        for (int i = parting + 1; i + 1 < toIt.size(); i++) {
            if (!entersOnSomeRun(toIt.get(i), toIt.get(i + 1), made)) {
                return Optional.empty();
            }
        }
        List<Core> some = workedOutUpTo(root, made, false);
        List<Core> every = workedOutUpTo(root, made, true);
        if (some == null || every == null) {
            return Optional.empty();
        }
        List<Core> ofIt = Evaluated.inOrder(made).stream().map(Evaluated.Step::expression)
                .toList();
        List<Core> onSomeRun = new ArrayList<>(some.subList(0, some.size() - 1));
        onSomeRun.addAll(ofIt);
        List<Core> onEveryRun = new ArrayList<>(every.subList(0, every.size() - 1));
        onEveryRun.addAll(ofIt);
        return Optional.of(new BeforeAConstruction(onSomeRun, onEveryRun));
    }

    /**
     * What a run works out before a construction it gets to ({@link #workedOutBeforeAConstruction}),
     * as two questions ask it.
     *
     * @param onSomeRun  every part a run getting to it may work out first, a part that runs only
     *                   on some runs counted as running, as {@link #nothingBeforeItEndsARun} counts
     *                   them, and what it is made of: what may end a run before it is in these
     * @param onEveryRun the parts every run getting to it works out first, and what it is made
     *                   of: what a run that gets to it has got past is in these
     */
    record BeforeAConstruction(List<Core> onSomeRun, List<Core> onEveryRun) {

        BeforeAConstruction {
            onSomeRun = List.copyOf(onSomeRun);
            onEveryRun = List.copyOf(onEveryRun);
        }

        /** Nothing worked out first: a run starting here. */
        static final BeforeAConstruction NOTHING = new BeforeAConstruction(List.of(), List.of());

        /** What this says is worked out first, and then what {@code after} says. */
        BeforeAConstruction then(BeforeAConstruction after) {
            List<Core> some = new ArrayList<>(onSomeRun);
            some.addAll(after.onSomeRun());
            List<Core> every = new ArrayList<>(onEveryRun);
            every.addAll(after.onEveryRun());
            return new BeforeAConstruction(some, every);
        }
    }

    /** Whether {@code node} works {@code first} out on every run it runs on, before it enters
     *  {@code then}, on the way down to {@code made}. */
    private static boolean firstOnEveryRun(Core node, Core first, Core then, Core made) {
        return switch (node) {
            case Core.LetIn let -> first == let.value() && then == let.body();
            // A value standing as a wider type holds one, and two ways do not part at it; a
            // function value's body runs where it is applied, and not here.
            case Core.Widen _, Core.Block _ -> false;
            // What an attempt is built of is worked out before either arm, and is reached
            // through the construction; the construction itself is the attempt's own deciding.
            case Core.IfConstructed attempt ->
                    first == attempt.construct() && first != made;
            default -> {
                for (Evaluated.Step step : Evaluated.inOrder(node)) {
                    if (step.expression() == then) {
                        yield false;
                    }
                    if (step.expression() == first) {
                        yield step instanceof Evaluated.Step.Always;
                    }
                }
                yield false;
            }
        };
    }

    /** Whether {@code node} enters {@code child} on some run it runs on, on the way down to
     *  {@code made}: every part of it but a function value's body, which runs where it is
     *  applied, and the construction an attempt tests, which is the attempt's own deciding. */
    private static boolean entersOnSomeRun(Core node, Core child, Core made) {
        return switch (node) {
            // A value standing as a wider type enters what it holds whenever it runs.
            case Core.Widen _ -> true;
            case Core.Block _ -> false;
            case Core.IfConstructed attempt -> child != attempt.construct() || child != made;
            default -> true;
        };
    }

    /**
     * What every run that reaches {@code comparison}, a node of {@code root}'s tree, has worked out
     * by then — the comparison included — or none where it is not in the tree, or stands in a
     * closure.
     */
    static List<Core> alwaysWorkedOutUpTo(Core root, Core comparison) {
        List<Core> worked = root == null ? null : workedOutUpTo(root, comparison, true);
        return worked == null ? List.of() : worked;
    }

    /**
     * What every run reaching {@code comparison}, a node of {@code root}'s tree, at the first
     * application of each closure it stands in has worked out by then, the comparison included,
     * and the calls applying those closures — none where it stands in no closure, and null where
     * it is not in the tree or stands in a closure no call it is handed to applies.
     *
     * <p>The first application of a closure comes after whatever its call is handed beside it, and
     * after nothing of the closure's body: the parts of the body before the comparison are worked
     * out as anywhere else.
     */
    static FirstApplication workedOutAtTheFirstApplication(Core root, Core comparison) {
        List<Core> way = root == null ? null : wayDownTo(root, comparison);
        if (way == null) {
            return null;
        }
        List<Core> out = new ArrayList<>();
        List<Applying> entered = new ArrayList<>();
        for (int i = 0; i + 1 < way.size(); i++) {
            Core child = way.get(i + 1);
            switch (way.get(i)) {
                case Core.Block block -> {
                    Core applying = i == 0 ? null : way.get(i - 1);
                    if (applying == null || Within.argumentsOf(applying).stream()
                            .noneMatch(arg -> Core.withoutStanding(arg) == block)) {
                        return null;
                    }
                    // Whole, a closure beside this one included: which of the closures a call is
                    // handed it applies first is the call's, and one applied before this one has
                    // run its body by then.
                    for (Core arg : Within.argumentsOf(applying)) {
                        if (Core.withoutStanding(arg) != block
                                && out.stream().noneMatch(part -> part == arg)) {
                            out.add(arg);
                        }
                    }
                    entered.add(new Applying(applying, block));
                }
                case Core.Widen _ -> { }
                case Core.LetIn let -> {
                    if (child == let.body()) {
                        workedOut(out, let.value());
                    }
                }
                case Core.IfConstructed attempt when child == attempt.construct() -> { }
                case Core node -> {
                    for (Evaluated.Step step : Evaluated.inOrder(node)) {
                        if (step.expression() == child) {
                            break;
                        }
                        if (step instanceof Evaluated.Step.Always) {
                            workedOut(out, step.expression());
                        }
                    }
                }
            }
        }
        out.add(comparison);
        return new FirstApplication(List.copyOf(out), List.copyOf(entered));
    }

    /**
     * What a run works out up to a comparison at the first application of each closure it stands
     * in ({@link #workedOutAtTheFirstApplication}).
     *
     * @param parts   what it works out, in order, the comparison last
     * @param entered each closure the comparison stands in, outermost first, with the call
     *                applying it
     */
    record FirstApplication(List<Core> parts, List<Applying> entered) {}

    /** A closure on the way to a comparison, and the call it is handed to. */
    record Applying(Core call, Core.Block closure) {}

    /**
     * Files {@code e} as worked out on the way to a comparison, unless it is a function value.
     * What a node evaluates before the part the way goes down through, and the value of a
     * {@code let} the way goes into the body of, come through here, so what a closure written
     * there is taken for is said once. The call a closure is handed to, and the arguments beside
     * the closure, are filed whole where the way enters the closure.
     *
     * <p>Evaluating a closure makes the function and runs nothing of its body. The body runs
     * where a call applies the function, and a call handed the closure beside the argument the
     * comparison stands in applies it after every argument, that one included ({@link Evaluated}).
     * A closure bound by a {@code let} is the same value: what its body does is the call that
     * applies the name, which is its own step where it comes.
     */
    private static void workedOut(List<Core> out, Core e) {
        workedOut(out, e, false);
    }

    /** The same, a function value filed as well where {@code withFunctionValues}. */
    private static void workedOut(List<Core> out, Core e, boolean withFunctionValues) {
        if (withFunctionValues || !Evaluated.makesAFunction(e)) {
            out.add(e);
        }
    }

    /** The nodes from {@code e} down to {@code node}, both included, by identity — or null where
     *  {@code node} is not under {@code e}. */
    private static List<Core> wayDownTo(Core e, Core node) {
        if (e == node) {
            List<Core> out = new ArrayList<>();
            out.add(e);
            return out;
        }
        List<List<Core>> found = new ArrayList<>(1);
        Core.forEachChild(e, child -> {
            if (found.isEmpty()) {
                List<Core> below = wayDownTo(child, node);
                if (below != null) {
                    found.add(below);
                }
            }
        });
        if (found.isEmpty()) {
            return null;
        }
        List<Core> out = found.getFirst();
        out.addFirst(e);
        return out;
    }
}
