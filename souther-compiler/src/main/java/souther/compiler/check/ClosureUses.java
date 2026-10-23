package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.semantics.Combinator;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.types.BindingId;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * Every use of one closure of a body: each application one of the language's operations makes of
 * it, and whether anything else uses it as well ({@link ClosureEntries}).
 *
 * <p>Each application and not the containers alone. Which containers enter the closure is one
 * question about these; how far each operation goes applying it, and which operation that is, are
 * others, and a reader asking them asks the same applications rather than finding them again.
 *
 * @param applications   each application an operation makes of the closure, in the order the body
 *                       holds them
 * @param usedElsewhere  whether something other than an operation applying it uses the closure —
 *                       applies it directly, hands it to a function of the author's, keeps it in a
 *                       value — which needs no container to run it
 */
public record ClosureUses(List<Application> applications, boolean usedElsewhere) {

    public ClosureUses {
        applications = List.copyOf(applications);
    }

    /**
     * One application an operation makes of the closure.
     *
     * @param operation what the call applies
     * @param lineage   which copy of a body the call stands in, which says what the author called
     *                  where the call is inside the body of something expanded where they did
     * @param container what the operation walks
     * @param applied   how far the operation goes applying the closure
     * @param call      the call that applies it, which a reader of the closure's parameters asks
     *                  what else the operation hands the closure ({@link SeededWalk#of})
     * @param position  the binding the closure is handed the element's position on, counted from
     *                  nought in the order {@code container} holds its elements — or null where the
     *                  operation is shown to hand it none ({@link Combinator#positionParam})
     * @param step      the closure as the block it is, whose body runs on each application
     * @param held      the bindings the closure is handed what {@code container} holds on: the
     *                  element, and the key a map files it under
     */
    public record Application(ValueName operation, OccurrenceLineage lineage, Core container,
                              HowAClosureIsApplied applied, Core call, BindingId position,
                              Core.Block step, Set<BindingId> held) {

        public Application {
            Objects.requireNonNull(operation, "an application is some operation's");
            Objects.requireNonNull(lineage, "a call stands in some copy of a body");
            Objects.requireNonNull(container, "an operation walks some container");
            Objects.requireNonNull(applied, "and applies the closure some way");
            Objects.requireNonNull(call, "by some call");
            Objects.requireNonNull(step, "a closure an operation applies is a block it reads");
            held = Set.copyOf(held);
            if (position != null && !parameterOf(step, position)) {
                throw new IllegalArgumentException("the position is handed to a parameter of the"
                        + " closure applied: " + position);
            }
            for (BindingId each : held) {
                if (!parameterOf(step, each) || each.equals(position)) {
                    throw new IllegalArgumentException("what the container holds is handed to a"
                            + " parameter of the closure, apart from the position: " + each);
                }
            }
        }

        /**
         * The parameters whose value at one application the applications before it make: every one
         * the closure is not handed what the container holds on — the position, which counts them,
         * and what a walk carries from one to the next. Past the first element, a run hands them
         * only where it got through every application before.
         */
        public Set<BindingId> madeByTheApplicationsBefore() {
            Set<BindingId> out = new LinkedHashSet<>();
            for (Core.Binder param : step.params()) {
                if (param != null && param.binding() != null && !held.contains(param.binding())) {
                    out.add(param.binding());
                }
            }
            return out;
        }

        private static boolean parameterOf(Core.Block step, BindingId binding) {
            return step.params().stream()
                    .anyMatch(param -> param != null && binding.equals(param.binding()));
        }
    }

    /** The containers the closure is entered over, one for each operation applying it, or none
     *  where something other than an operation may apply it. */
    public List<Core> enteredOver() {
        if (usedElsewhere) {
            return List.of();
        }
        List<Core> out = new ArrayList<>();
        for (Application each : applications) {
            if (out.stream().noneMatch(container -> container == each.container())) {
                out.add(each.container());
            }
        }
        return List.copyOf(out);
    }
}
