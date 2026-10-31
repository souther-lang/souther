package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A reading of a body narrows a region by a run's answers once ({@link RegionsGotPast}): asked of
 * the same region and the same answers again, it hands back what it worked out, and asked of
 * others, however alike, it works them out.
 */
class ARegionIsNarrowedOnceInAReadingByTheSameAnswersTest {

    /** A region nothing here asks anything of: the narrowing is the supplier's. */
    private static final class Untouched implements SearchRegion {

        @Override
        public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
            throw new UnsupportedOperationException();
        }

        @Override
        public SearchRegion assuming(NumericTerm.FromOnePosition term, Place at, Rel rel) {
            throw new UnsupportedOperationException();
        }

        @Override
        public SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at) {
            throw new UnsupportedOperationException();
        }

        @Override
        public PlacesApart apartAt(NumericTerm.FromOnePosition term) {
            throw new UnsupportedOperationException();
        }

        @Override
        public SearchRegion given(Map<NumericTerm, Place> fixed) {
            throw new UnsupportedOperationException();
        }

        @Override
        public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Optional<EmptyInput> emptiness() {
            throw new UnsupportedOperationException();
        }
    }

    private static DemandReading.Answered answered() {
        return new DemandReading.Answered(List.of(new TakenConstraint.Affine(
                LinearForm.atom(new NumericTerm.ValueOf(TermPath.of("x"))), Rel.GE)),
                List.of(), false);
    }

    /** A narrowing that counts how often it is worked out. */
    private static final class Counted implements Supplier<Reachability.Reaching.NarrowedPast> {

        private final SearchRegion region;
        private int times;

        Counted(SearchRegion region) {
            this.region = region;
        }

        @Override
        public Reachability.Reaching.NarrowedPast get() {
            times++;
            return new Reachability.Reaching.NarrowedPast(List.of(), region, false);
        }
    }

    @Test
    void theSameRegionByTheSameAnswersIsNarrowedOnce() {
        SearchRegion region = new Untouched();
        DemandReading.Answered answered = answered();
        Counted narrowing = new Counted(region);
        RegionsGotPast.over(() -> {
            Reachability.Reaching.NarrowedPast first =
                    RegionsGotPast.of(region, answered, narrowing);
            assertSame(first, RegionsGotPast.of(region, answered, narrowing));
            return null;
        });
        assertEquals(1, narrowing.times);
    }

    @Test
    void answersEqualToThemButOthersAreWorkedOutForThemselves() {
        SearchRegion region = new Untouched();
        DemandReading.Answered one = answered();
        DemandReading.Answered other = answered();
        assertEquals(one, other, "alike");
        Counted narrowing = new Counted(region);
        RegionsGotPast.over(() -> {
            RegionsGotPast.of(region, one, narrowing);
            RegionsGotPast.of(region, other, narrowing);
            return null;
        });
        assertEquals(2, narrowing.times);
    }

    @Test
    void anotherRegionByTheSameAnswersIsWorkedOutForItself() {
        DemandReading.Answered answered = answered();
        SearchRegion one = new Untouched();
        SearchRegion other = new Untouched();
        Counted narrowing = new Counted(one);
        RegionsGotPast.over(() -> {
            RegionsGotPast.of(one, answered, narrowing);
            RegionsGotPast.of(other, answered, narrowing);
            return null;
        });
        assertEquals(2, narrowing.times);
    }

    @Test
    void outsideAReadingEveryRegionIsNarrowedWhenAsked() {
        SearchRegion region = new Untouched();
        DemandReading.Answered answered = answered();
        Counted narrowing = new Counted(region);
        assertNotSame(RegionsGotPast.of(region, answered, narrowing),
                RegionsGotPast.of(region, answered, narrowing));
        assertEquals(2, narrowing.times);
    }
}
