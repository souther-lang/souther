package souther.compiler.partition;

import souther.compiler.check.ClosureUses;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.core.WhatABodyReads;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Whether every row a count is read over gets past what a run works out before the comparison
 * reading it, as the witness of the count did.
 *
 * <p>The rows are the witness's two elements over again, so many of each, with everything else the
 * witness holds. What a run works out before the comparison and reads nothing of the container is
 * worked out on what the witness holds, and comes out as it did there. What reads the container
 * is allowed in one shape only: the walk whose kept elements the comparison counts, applying a
 * step to every element and handing it the element alone, with nothing carried from one
 * application to the next and nothing of the container read inside it. Each application is then
 * of an element the witness held, on what the witness held besides, and comes out as it did
 * there; and what the walk keeps is never more than the container holds. Anything else read off
 * the container before the comparison — a fold, a lookup, a helper walking it — is worked out on
 * a container the witness never held, and nothing here says it comes out at all.
 *
 * <p>Of the tree the analysis reads, where the language's operations stand as the calls they are.
 */
final class WhatARunWorksOutBeforeACount {

    private WhatARunWorksOutBeforeACount() {}

    /**
     * {@code witnesses}, kept for a count only where every row it is read over gets past what a
     * run works out before {@code comparison}, a node of {@code root}'s tree; none where
     * {@code comparison} is not in it, or stands in a closure, whose applications are not the one
     * run a witness is of.
     *
     * @param parameters the binding each parameter of the behavior is read on, by its name
     */
    static CountWitnesses.Lookup past(Core root, Core comparison, InputReads reads,
                                      Map<BindingId, String> parameters,
                                      CountWitnesses.Lookup witnesses) {
        List<Before> before = root == null ? null : before(root, comparison);        if (before == null) {
            return CountWitnesses.Lookup.NONE;
        }
        return count -> count.container() instanceof DecisionSubject.AnInput(TermPath container)
                && getsPast(before, comparison, root, reads, parameterOf(container, parameters))
                ? witnesses.of(count) : CountWitnesses.Sought.NOTHING;
    }

    /** What a run works out before the comparison: an expression, and the name a {@code let}
     *  gives it, or null where it is given none. */
    private record Before(Core value, BindingId named) {}

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
     * Whether every part of {@code before} reading the container on {@code parameter} is the walk
     * whose kept elements {@code comparison} counts.
     */
    private static boolean getsPast(List<Before> before, Core comparison, Core root,
                                    InputReads reads, BindingId parameter) {
        if (parameter == null) {
            return false;
        }
        Set<BindingId> ofTheContainer = WhatABodyReads.namesMadeOf(root, Set.of(parameter));
        for (Before each : before) {
            if (WhatABodyReads.anyOf(each.value(), ofTheContainer)
                    && !keptAndCounted(each, comparison, reads, parameter, ofTheContainer)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether {@code each} is a walk over the container on {@code parameter} that the comparison
     * reads what it kept of: a call handed the container as it is and one closure, which the call
     * alone applies, to every element, handed the element and nothing an application before it
     * made, and reading nothing of the container.
     */
    private static boolean keptAndCounted(Before each, Core comparison, InputReads reads,
                                          BindingId parameter, Set<BindingId> ofTheContainer) {
        Core call = Core.withoutStanding(each.value());
        List<Core> args = switch (call) {
            case Core.Call applying -> applying.args();
            case Core.PreservedCall applying -> applying.args();
            default -> null;
        };
        if (each.named() == null || !WhatABodyReads.binding(comparison, each.named())
                || args == null) {
            return false;
        }
        Core.Block step = null;
        for (Core arg : args) {
            Core bare = Core.withoutStanding(arg);
            if (bare instanceof Core.Block block && step == null) {
                step = block;
            } else if (!offTheParameter(bare, parameter)
                    && WhatABodyReads.anyOf(arg, ofTheContainer)) {
                return false;
            }
        }
        ClosureUses uses = step == null ? null : reads.usesOf(step);
        if (uses == null || uses.usedElsewhere() || uses.applications().size() != 1
                || WhatABodyReads.anyOf(step.body(), ofTheContainer)) {
            return false;
        }
        ClosureUses.Application applied = uses.applications().getFirst();
        return applied.applied() == HowAClosureIsApplied.TO_EVERY_ELEMENT
                && applied.call() == call
                && applied.madeByTheApplicationsBefore().isEmpty()
                && offTheParameter(applied.container(), parameter);
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
     * What a run works out before it gets to {@code comparison}, a node of {@code e}'s tree, in
     * the order it does — or null where it is not in the tree, or stands in a closure.
     *
     * <p>The value of every {@code let} whose body it is in, and every part of each node on the
     * way that runs before the part it is in: an operand before it, a condition deciding the
     * branch it is in. A part that runs only on some runs is counted as running, which asks more
     * of the way and never less.
     */
    private static List<Before> before(Core e, Core comparison) {
        if (e == comparison) {
            return new ArrayList<>();
        }
        Core bare = Core.withoutStanding(e);
        if (bare instanceof Core.Block) {
            return null;
        }
        if (bare instanceof Core.LetIn let) {
            if (holds(let.value(), comparison)) {
                return before(let.value(), comparison);
            }
            List<Before> inside = holds(let.body(), comparison)
                    ? before(let.body(), comparison) : null;
            if (inside == null) {
                return null;
            }
            inside.addFirst(new Before(let.value(),
                    let.binder() == null ? null : let.binder().binding()));
            return inside;
        }
        List<Core> children = new ArrayList<>();
        Core.forEachChild(e, children::add);
        for (Core child : children) {
            if (!holds(child, comparison)) {
                continue;
            }
            List<Before> inside = before(child, comparison);
            if (inside == null) {
                return null;
            }
            List<Before> earlier = new ArrayList<>();
            for (Evaluated.Step step : Evaluated.inOrder(e)) {
                if (step.expression() == child) {
                    break;
                }
                earlier.add(new Before(step.expression(), null));
            }
            earlier.addAll(inside);
            return earlier;
        }
        return null;
    }

    /** Whether {@code node} is {@code e} or anywhere inside it. */
    private static boolean holds(Core e, Core node) {
        if (e == node) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] = found[0] || holds(child, node));
        return found[0];
    }
}
