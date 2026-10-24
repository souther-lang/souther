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
import java.util.HashMap;
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
    static CountWitnesses.Lookup past(Core root, Core comparison, InputReads reads,
                                      Supplier<Map<Quantity.HowManyMeet, Core>> readOff,
                                      Map<BindingId, String> parameters,
                                      CountWitnesses.Lookup witnesses) {
        if (root == null) {
            return CountWitnesses.Lookup.NONE;
        }
        Map<Quantity.HowManyMeet, Boolean> getsThrough = new HashMap<>();
        List<Optional<List<Core>>> worked = new ArrayList<>(1);
        return count -> {
            if (worked.isEmpty()) {
                worked.add(Optional.ofNullable(workedOutUpTo(root, comparison, false)));
            }
            boolean through = worked.getFirst().isPresent()
                    && getsThrough.computeIfAbsent(count, asked -> getsThrough(
                            worked.getFirst().get(), asked, readOff.get().get(asked), root,
                            reads, parameters));
            return through ? witnesses.of(count) : CountWitnesses.Sought.NOTHING;
        };
    }

    /** Whether every one of {@code parts} is let through for {@code count}, read off
     *  {@code counted} — never where the reading names no call it was read off. */
    private static boolean getsThrough(List<Core> parts, Quantity.HowManyMeet count,
                                       Core counted, Core root, InputReads reads,
                                       Map<BindingId, String> parameters) {
        if (counted == null
                || !(count.container() instanceof DecisionSubject.AnInput(TermPath container))) {
            return false;
        }
        BindingId parameter = parameterOf(container, parameters);
        if (parameter == null) {
            return false;
        }
        Within asked = new Within(parameter,
                WhatABodyReads.namesMadeOf(root, Set.of(parameter)), reads,
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
            if (uses == null || uses.usedElsewhere() || uses.applications().size() != 1
                    || WhatABodyReads.anyOf(step.body(), ofTheContainer)) {
                return false;
            }
            ClosureUses.Application applied = uses.applications().getFirst();
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
                        out.add(let.value());
                    }
                }
                case Core node -> {
                    for (Evaluated.Step step : Evaluated.inOrder(node)) {
                        if (step.expression() == child) {
                            break;
                        }
                        if (!onlyWhatAlwaysRuns || step instanceof Evaluated.Step.Always) {
                            out.add(step.expression());
                        }
                    }
                }
            }
        }
        out.add(comparison);
        return out;
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
                        out.add(let.value());
                    }
                }
                case Core node -> {
                    for (Evaluated.Step step : Evaluated.inOrder(node)) {
                        if (step.expression() == child) {
                            break;
                        }
                        if (step instanceof Evaluated.Step.Always) {
                            out.add(step.expression());
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
