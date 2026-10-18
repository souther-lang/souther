package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

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
     */
    public record Application(ValueName operation, OccurrenceLineage lineage, Core container,
                              HowAClosureIsApplied applied, Core call) {

        public Application {
            Objects.requireNonNull(operation, "an application is some operation's");
            Objects.requireNonNull(lineage, "a call stands in some copy of a body");
            Objects.requireNonNull(container, "an operation walks some container");
            Objects.requireNonNull(applied, "and applies the closure some way");
            Objects.requireNonNull(call, "by some call");
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
