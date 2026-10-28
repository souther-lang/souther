package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Narrowing a base by a list of steps comes to the fold of the list over the base, whichever lists
 * were asked before it, and redoes only the steps past the nearest one kept.
 */
class ARegionNarrowedByAListStartingAlikeIsTheFoldOfItTest {

    /** A region that is the steps taken in so far, so that two folds are equal where they took in
     *  the same steps in the same order. */
    private record Trail(List<Integer> taken, NarrowingsKept kept) implements SearchRegion {

        @Override
        public NarrowingsKept narrowingsKept() {
            return kept;
        }

        @Override
        public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
            return new Assumption.Taken(this);
        }

        @Override
        public SearchRegion assuming(NumericTerm.FromOnePosition term, Place at, Rel rel) {
            return this;
        }

        @Override
        public SearchRegion given(Map<NumericTerm, Place> fixed) {
            return this;
        }

        @Override
        public SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at) {
            return this;
        }

        @Override
        public PlacesApart apartAt(NumericTerm.FromOnePosition term) {
            return PlacesApart.NONE;
        }

        @Override
        public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
            return new NumericDomain.FormProjection.NothingIsLeft();
        }

        @Override
        public Optional<EmptyInput> emptiness() {
            return Optional.empty();
        }
    }

    private static final Trail NOTHING_TAKEN = new Trail(List.of(), NarrowingsKept.NONE);

    private static Trail base(NarrowingsKept kept) {
        return new Trail(List.of(), kept);
    }

    private static Trail through(Trail base, List<Integer> steps, AtomicInteger applied) {
        return (Trail) base.narrowingsKept().through(base, steps, (step, region) -> {
            applied.incrementAndGet();
            List<Integer> taken = new ArrayList<>(((Trail) region).taken());
            taken.add(step);
            return new Trail(List.copyOf(taken), base.kept());
        });
    }

    @Test
    void anyListAskedAfterAnyOthersComesToTheStepsTakenInInOrder() {
        // A small alphabet and lists of every length up to past the interval kept at, so that
        // lists share leading runs of every length, the whole of one, and none.
        Random random = new Random(2781);
        NarrowingsKept kept = new NarrowingsKept();
        Trail base = base(kept);
        for (int ask = 0; ask < 3000; ask++) {
            List<Integer> steps = new ArrayList<>();
            int length = random.nextInt(21);
            for (int at = 0; at < length; at++) {
                steps.add(random.nextInt(2));
            }
            assertEquals(steps, through(base, steps, new AtomicInteger()).taken());
        }
    }

    @Test
    void aListExtendingOneJustAskedRedoesOnlyThePastTheNearestStepKept() {
        NarrowingsKept kept = new NarrowingsKept();
        Trail base = base(kept);
        List<Integer> ten = List.of(1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
        List<Integer> twelve = List.of(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);
        AtomicInteger first = new AtomicInteger();
        through(base, ten, first);
        assertEquals(10, first.get());
        // Kept at every fourth step, so the eighth is the nearest kept below the twelfth and the
        // four steps past it are taken in, where the fold would take twelve.
        AtomicInteger second = new AtomicInteger();
        assertEquals(twelve, through(base, twelve, second).taken());
        assertEquals(4, second.get());
        // The same list again is not folded at all.
        AtomicInteger again = new AtomicInteger();
        assertEquals(twelve, through(base, twelve, again).taken());
        assertEquals(0, again.get());
    }

    @Test
    void aListWhoseLeadingRunWasNeverAskedIsFoldedFromTheBase() {
        NarrowingsKept kept = new NarrowingsKept();
        Trail base = base(kept);
        through(base, List.of(1, 2, 3, 4, 5, 6), new AtomicInteger());
        AtomicInteger applied = new AtomicInteger();
        assertEquals(List.of(9, 2, 3, 4, 5, 6),
                through(base, List.of(9, 2, 3, 4, 5, 6), applied).taken());
        assertEquals(6, applied.get());
    }

    @Test
    void whatIsKeptIsBoundedSoTheOldestListIsFoldedAgainFromTheBase() {
        NarrowingsKept kept = new NarrowingsKept();
        Trail base = base(kept);
        List<Integer> first = List.of(0, 0, 0, 0, 0, 0, 0, 0);
        through(base, first, new AtomicInteger());
        for (int other = 1; other <= 200; other++) {
            through(base, List.of(other, other, other, other, other, other, other, other),
                    new AtomicInteger());
        }
        AtomicInteger applied = new AtomicInteger();
        assertEquals(first, through(base, first, applied).taken());
        assertEquals(first.size(), applied.get());
    }

    @Test
    void aRegionThatKeepsNothingFoldsEveryListFromItself() {
        Trail base = NOTHING_TAKEN;
        List<Integer> steps = List.of(1, 2, 3, 4, 5);
        through(base, steps, new AtomicInteger());
        AtomicInteger applied = new AtomicInteger();
        assertEquals(steps, through(base, steps, applied).taken());
        assertEquals(steps.size(), applied.get());
    }
}
