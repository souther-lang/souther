package souther.compiler.partition;

import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * The assignments a point was already composed from, whose rows did not stand at it.
 *
 * <p><b>What a search did and not what a rule says.</b> An assignment is here because a row was
 * built from it and read back somewhere other than the point it was built for — which is this
 * compiler having looked, and is no part of what the model leaves the positions. Written into the
 * item's own exclusions instead, a search's history would become a condition of the criterion, and
 * the next reader of that criterion would be told the model refuses a value nothing refuses.
 *
 * <p><b>An assignment and not a value.</b> What did not stand is everything the row was built from
 * standing together, so nothing here rules out a place on its own. The same place with the rest of
 * them standing somewhere else is a thing nothing has tried: refused there too, a search would give
 * up a point it had a row for, and say a value was exhausted on the strength of a row built
 * somewhere else.
 *
 * <p><b>Which is why there are two ways to ask.</b> A search that reaches a whole assignment before
 * anything is built asks whether this is one of them ({@link #holds}); one that settles a position
 * at a time, with the rest of them already standing, asks what that position may not be offered
 * ({@link #apartFor}) — and the second is the first, projected onto what such a caller knows.
 *
 * <p>Not the rows and not the witnesses. Nothing here has been certified, so the word for what was
 * built cannot be the word for what answers the point; and a row is what an assignment was built
 * into rather than the thing to leave out next time.
 */
public record ValuesTried(List<Map<RealizationTarget, Place>> rejected) {

    /** Nothing has been tried, which is where every search for a point starts. */
    public static final ValuesTried NONE = new ValuesTried(List.of());

    public ValuesTried {
        List<Map<RealizationTarget, Place>> copied = new ArrayList<>();
        rejected.forEach(one -> copied.add(Map.copyOf(one)));
        rejected = List.copyOf(copied);
    }

    /**
     * Whether {@code assignment} is one a row was already built from and did not stand.
     *
     * <p>The whole of it and every target of it. A walk that reaches an assignment has chosen for
     * all of them at once, and what did not stand is that — so this is the question such a walk
     * has, and the one that leaves every other assignment it could reach still to be reached.
     */
    public boolean holds(Map<RealizationTarget, Place> assignment) {
        return rejected.stream().anyMatch(each -> standingAlike(each, assignment));
    }

    /**
     * The places this target is not to be offered, where the rest of them stand as {@code given}
     * says.
     *
     * <p>A target {@code given} says nothing about leaves the assignment standing. What is known of
     * an asking is what it carries, and a caller that settles one target at a time knows the others
     * only as it reaches them — held to naming all of them, the exclusion would be spent on the
     * first asking and the same place offered for the rest of the search.
     *
     * <p><b>So this is for a caller whose others are already standing.</b> Asked before they are —
     * with {@code given} empty where the rest of them are still to be chosen — what comes back
     * rules a place out of arrangements nothing has tried. A search that chooses for all of them
     * asks {@link #holds} and keeps every arrangement it has not reached.
     */
    public PlacesApart apartFor(RealizationTarget target, Map<RealizationTarget, Place> given) {
        List<Place> apart = new ArrayList<>();
        for (Map<RealizationTarget, Place> one : rejected) {
            Place was = one.get(target);
            if (was != null && standingAs(one, target, given)) {
                apart.add(was);
            }
        }
        return PlacesApart.of(apart);
    }

    /** Whether two arrangements stand the same targets at the same places on their orders. */
    private static boolean standingAlike(Map<RealizationTarget, Place> one,
                                         Map<RealizationTarget, Place> other) {
        if (!one.keySet().equals(other.keySet())) {
            return false;
        }
        return one.entrySet().stream()
                .allMatch(each -> each.getValue().sameAs(other.get(each.getKey())));
    }

    /** Whether the rest of a rejected assignment stands where {@code given} has it standing. */
    private static boolean standingAs(Map<RealizationTarget, Place> one, RealizationTarget target,
                                      Map<RealizationTarget, Place> given) {
        for (Map.Entry<RealizationTarget, Place> beside : one.entrySet()) {
            if (beside.getKey().equals(target)) {
                continue;
            }
            Place now = given.get(beside.getKey());
            // On the order and not on the spelling: a place standing where another was tried is the
            // same standing whichever of the two ways it was written down.
            if (now != null && !now.sameAs(beside.getValue())) {
                return false;
            }
        }
        return true;
    }

    /**
     * The same, with what {@code fixing} put the targets at remembered as one assignment.
     *
     * <p>All of them together and not the one a reader thinks was chosen. Which target's value the
     * row turned on is not something the fixing says, and a search that guessed would go on offering
     * the arrangement it did not exclude.
     *
     * <p>Each place as the search composed it, and told from another on the order. Two arrangements
     * differ where they stand different places and not where one of them was written differently —
     * asked of what holds them, the same arrangement written two ways would be two, and a point
     * would spend on one value what it is allowed for two.
     */
    public ValuesTried and(Map<RealizationTarget, Place> fixing) {
        if (fixing.isEmpty() || holds(fixing)) {
            return this;
        }
        List<Map<RealizationTarget, Place>> next = new ArrayList<>(rejected);
        next.add(fixing);
        return new ValuesTried(next);
    }
}
