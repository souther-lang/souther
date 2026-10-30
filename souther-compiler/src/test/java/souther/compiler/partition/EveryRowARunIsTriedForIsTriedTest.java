package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The rows a number only a run works out is looked for with are every candidate of a small
 * population, all of them asked for, and offered only where the rules were not shown to leave
 * nothing.
 *
 * <p>The population and how many of it are asked for are one decision, said in one place: cut at a
 * figure laid down elsewhere, the order the candidates come in decides which of them are ever
 * tried, and a size or a value in the population is one no search reaches. The order decides
 * only how soon, and each size is tried at every value before the next.
 */
class EveryRowARunIsTriedForIsTriedTest {

    private static final NumericTerm.FromOnePosition LENGTH =
            new NumericTerm.ValueOf(TermPath.of("xs"));

    private static final NumericTerm.FromOnePosition NUMBER =
            new NumericTerm.ValueOf(TermPath.of("n"));

    private static PointSearchGoal.ByObservation goal(List<NumericTerm.FromOnePosition> lengths,
                                                      List<NumericTerm.FromOnePosition> values) {
        return new PointSearchGoal.ByObservation(lengths, values,
                new Criterion.AtTheLevel(new Level.OfTheQuantity(ExactRatio.ZERO)));
    }

    private static Place at(Map<RealizationTarget, Place> candidate,
                            NumericTerm.FromOnePosition term) {
        return candidate.get(RealizationTarget.of(term));
    }

    /** Every size with every value, once each, and every one of them asked for. */
    @Test
    void everySizeWithEveryValueIsACandidateAndEveryCandidateIsAsked() {
        PointSearchGoal.ByObservation both = goal(List.of(LENGTH), List.of(NUMBER));
        List<Map<RealizationTarget, Place>> candidates = RowsARunIsTriedFor.candidates(both);

        Set<List<Place>> pairs = new HashSet<>();
        candidates.forEach(each -> pairs.add(List.of(at(each, LENGTH), at(each, NUMBER))));
        assertEquals(candidates.size(), pairs.size(), "no candidate twice");
        for (int size = 0; size <= 6; size++) {
            for (long value : List.of(0L, 1L, -1L, 2L)) {
                assertTrue(pairs.contains(List.of(Count.of(size), Count.of(value))),
                        size + " elements at " + value);
            }
        }
        assertEquals(candidates.size(), both.askedAtMost(),
                "every candidate is asked for, and no figure laid down elsewhere cuts them");
    }

    /** A size is tried at every value before the next size is. */
    @Test
    void eachSizeIsTriedAtEveryValueBeforeTheNext() {
        List<Map<RealizationTarget, Place>> candidates =
                RowsARunIsTriedFor.candidates(goal(List.of(LENGTH), List.of(NUMBER)));

        for (int i = 0; i < 4; i++) {
            assertEquals(Count.of(0), at(candidates.get(i), LENGTH), candidates.toString());
        }
        assertEquals(Count.of(1), at(candidates.get(4), LENGTH), candidates.toString());
    }

    /** One dimension alone is every value of it, asked for; none is asked once and has none. */
    @Test
    void oneDimensionAloneIsEveryValueOfIt() {
        assertEquals(7, RowsARunIsTriedFor.candidates(goal(List.of(LENGTH), List.of())).size());
        assertEquals(4, RowsARunIsTriedFor.candidates(goal(List.of(), List.of(NUMBER))).size());
        PointSearchGoal.ByObservation none = goal(List.of(), List.of());
        assertEquals(List.of(), RowsARunIsTriedFor.candidates(none));
        assertEquals(1, none.askedAtMost());
    }

    /** A region the rules leave nothing in holds no row, solved for or run: that is proved, and
     *  not said as a candidate missing. */
    @Test
    void aRegionLeftNothingIsProvedToHoldNoRowRun() {
        Realization answered = new LevelRealizer().realize(
                goal(List.of(LENGTH), List.of(NUMBER)), new NothingLeft(),
                NothingTheDeclarationsNarrow.LOOKING, ValuesTried.NONE);

        assertInstanceOf(Realization.Impossible.class, answered);
    }

    /** A region the rules were shown to leave nothing in, and nothing else asked of it. */
    private static final class NothingLeft implements SearchRegion {

        @Override
        public Optional<EmptyInput> emptiness() {
            return Optional.of(new EmptyInput.TwoValuesAtOnePosition(NUMBER, Count.of(0),
                    Count.of(1)));
        }

        @Override
        public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
            throw new UnsupportedOperationException("nothing is asked of an empty region");
        }

        @Override
        public SearchRegion assuming(NumericTerm.FromOnePosition term, Place at, Rel rel) {
            throw new UnsupportedOperationException("nothing is asked of an empty region");
        }

        @Override
        public SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at) {
            throw new UnsupportedOperationException("nothing is asked of an empty region");
        }

        @Override
        public PlacesApart apartAt(NumericTerm.FromOnePosition term) {
            throw new UnsupportedOperationException("nothing is asked of an empty region");
        }

        @Override
        public SearchRegion given(Map<NumericTerm, Place> fixed) {
            throw new UnsupportedOperationException("nothing is asked of an empty region");
        }

        @Override
        public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
            throw new UnsupportedOperationException("nothing is asked of an empty region");
        }
    }
}
