package souther.compiler.check;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * One part of a clause that a construction has to establish.
 *
 * <p>Every part of them, which is why they are a list and not a set of readings. A clause read as a
 * bound in one part and as a term in another is not a clause either of those guards discharges: both
 * have to be, and a reader handed the two flattened together is told that either would do. The
 * routes inside one part are the alternatives — that is where "any of these" belongs, and it is the
 * shape {@link Predicates.Clause#dischargedBy} has.
 */
public sealed interface RequiredPart {

    /**
     * The check carried this part into one or more forms a guard can be held against.
     *
     * <p>Never empty. A part with no route is the other arm: what the check made nothing of is a
     * conclusion with a reason, and an empty set of routes would be that conclusion said by an
     * absence.
     */
    record Routed(Set<StaticRoute> routes) implements RequiredPart {

        public Routed {
            if (routes == null || routes.isEmpty()) {
                throw new IllegalArgumentException(
                        "a part the check carried has somewhere to have carried it");
            }
            // Insertion order: `Set.of` and `Set.copyOf` iterate in an order salted once per JVM
            // run, and these are shown to an author a line at a time.
            routes = Collections.unmodifiableSet(new LinkedHashSet<>(routes));
        }
    }

    /**
     * The reading finished and this part is outside what it reads, so no guard discharges it and the
     * run-time check on construction is the whole of its enforcement.
     *
     * <p>A conclusion, which is why it is a part rather than an arm of
     * {@link CapabilityResult}: the clause was read, and this is what came of one part of it. A
     * reading that did not finish concluded nothing about any part, and is
     * {@link CapabilityResult.AnalysisStopped}.
     */
    record OutsideTheFragment(FragmentReason why) implements RequiredPart {

        public OutsideTheFragment {
            if (why == null) {
                throw new IllegalArgumentException("a part the check stopped on says what stopped it");
            }
        }
    }
}
