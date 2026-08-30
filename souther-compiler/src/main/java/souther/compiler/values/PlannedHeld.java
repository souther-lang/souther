package souther.compiler.values;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * What a reading holds while the values it describes have not been worked out.
 *
 * <p>The same two shapes a finished reading has: nothing satisfies the rules, or these alternatives
 * do. What is different is what a box may hold — a description of a set rather than the set — so a
 * box here may turn out to stand for nothing, where a settled one never does.
 *
 * <p>A choice this reading cannot settle is not one of these. Which branch of a choice can be taken
 * decides what the whole reading holds and what its alternatives owe, so an unsettled choice is a
 * state of the reading and is held there ({@code PlannedValues.Choice}) rather than as a third
 * thing a box could be inside.
 *
 * @param <A> what a position is called
 */
sealed interface PlannedHeld<A> {

    /** Nothing satisfies the rules, and that is settled. */
    record Nothing<A>() implements PlannedHeld<A> {}

    /**
     * The alternatives the rules leave, none of which is known to admit nothing.
     *
     * <p>What each position holds across them is not worked out here, unlike the settled reading's:
     * a join of two descriptions is a description, so there is nothing to pay for and nothing to
     * decide.
     */
    record Alternatives<A>(Set<Box<A>> boxes) implements PlannedHeld<A> {

        public Alternatives {
            if (boxes.isEmpty()) {
                throw new IllegalArgumentException("a reading holding no alternative is Nothing");
            }
            boxes = Collections.unmodifiableSet(new LinkedHashSet<>(boxes));
        }
    }

    /**
     * One product: what each position may hold, with every combination of them standing.
     *
     * <p>A position admitting every value is left out, as in the settled reading. What is not
     * refused here is a side admitting nothing: whether a description admits anything is the
     * question this whole arrangement exists to put off, so a box may hold one and be dropped when
     * the answer arrives.
     */
    record Box<A>(Map<A, AdmittedPlan> at) {

        public Box {
            Map<A, AdmittedPlan> said = new LinkedHashMap<>();
            at.forEach((atom, plan) -> {
                if (!(plan instanceof AdmittedPlan.Everything)) {
                    said.put(atom, plan);
                }
            });
            at = Collections.unmodifiableMap(said);
        }

        AdmittedPlan get(A atom) {
            return at.getOrDefault(atom, AdmittedPlan.ANY);
        }
    }

    /** One alternative, which is what most readings hold. */
    static <A> PlannedHeld<A> one(Box<A> box) {
        return new Alternatives<>(Set.of(box));
    }
}
