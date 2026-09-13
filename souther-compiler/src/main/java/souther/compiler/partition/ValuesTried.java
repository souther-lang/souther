package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.LinkedHashMap;
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
 * <p><b>An assignment and not a value.</b> What did not stand is the positions standing together,
 * so a place is ruled out for the position it was taken for and for the places the rest of them
 * were standing at. The same place under a different arrangement of the others is a thing nothing
 * has tried: refused there too, a search would give up a point it had a row for, and say a value
 * was exhausted on the strength of a row built somewhere else.
 *
 * <p>Not the rows and not the witnesses. Nothing here has been certified, so the word for what was
 * built cannot be the word for what answers the point; and a row is what an assignment was built
 * into rather than the thing to leave out next time.
 */
public record ValuesTried(List<Map<NumericTerm.FromOnePosition, Place>> rejected) {

    /** Nothing has been tried, which is where every search for a point starts. */
    public static final ValuesTried NONE = new ValuesTried(List.of());

    public ValuesTried {
        List<Map<NumericTerm.FromOnePosition, Place>> copied = new ArrayList<>();
        rejected.forEach(one -> copied.add(Map.copyOf(one)));
        rejected = List.copyOf(copied);
    }

    /**
     * The places this position is not to be offered, where the rest of them stand as {@code given}
     * says.
     *
     * <p>A position {@code given} says nothing about leaves the assignment standing. What is known
     * of an asking is what it carries, and a caller that settles one position at a time knows the
     * others only as it reaches them — held to naming all of them, the exclusion would be spent on
     * the first asking and the same place offered for the rest of the search.
     */
    public List<Place> apartFor(NumericTerm.FromOnePosition term,
                                Map<NumericTerm.FromOnePosition, Place> given) {
        List<Place> apart = new ArrayList<>();
        for (Map<NumericTerm.FromOnePosition, Place> one : rejected) {
            Place was = one.get(term);
            if (was != null && standingAs(one, term, given) && !apart.contains(was)) {
                apart.add(was);
            }
        }
        return List.copyOf(apart);
    }

    /** Whether the rest of a rejected assignment stands where {@code given} has it standing. */
    private static boolean standingAs(Map<NumericTerm.FromOnePosition, Place> one,
                                      NumericTerm.FromOnePosition term,
                                      Map<NumericTerm.FromOnePosition, Place> given) {
        for (Map.Entry<NumericTerm.FromOnePosition, Place> beside : one.entrySet()) {
            if (beside.getKey().equals(term)) {
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
     * The same, with what {@code fixing} put the positions at remembered as one assignment.
     *
     * <p>All of them together and not the one a reader thinks was chosen. Which position's value the
     * row turned on is not something the fixing says, and a search that guessed would go on offering
     * the arrangement it did not exclude.
     */
    public ValuesTried and(Map<RealizationTarget, Place> fixing) {
        Map<NumericTerm.FromOnePosition, Place> one = new LinkedHashMap<>();
        fixing.forEach((target, place) -> {
            if (target.term().atOnePosition() instanceof NumericTerm.FromOnePosition at) {
                one.put(at, place);
            }
        });
        if (one.isEmpty() || rejected.contains(one)) {
            return this;
        }
        List<Map<NumericTerm.FromOnePosition, Place>> next = new ArrayList<>(rejected);
        next.add(one);
        return new ValuesTried(next);
    }
}
