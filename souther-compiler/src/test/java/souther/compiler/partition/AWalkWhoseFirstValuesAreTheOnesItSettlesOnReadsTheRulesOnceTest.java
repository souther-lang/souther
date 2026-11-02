package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.Emptiness;
import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A search over a form whose first value at every position is the one it settles on reads the rules
 * once for the whole assignment, and not once for each position fixed.
 *
 * <p>Counted, because what is found is the same either way — the first value of each position in
 * the order the search tries them, the last position solved — and what is held here is the work.
 * Each reading of the rules with a position fixed is a closure of every rule reaching the form's
 * positions, and a search of six positions that read them for each was most of what a witness cost.
 *
 * <p>The region is one that narrows nothing and runs every position from nought to ten, so the
 * rules cannot refuse a value the search tries, and what it reads is what it is asked for.
 */
class AWalkWhoseFirstValuesAreTheOnesItSettlesOnReadsTheRulesOnceTest {

    private static final NumericTerm.FromOnePosition X = position("p.x");
    private static final NumericTerm.FromOnePosition Y = position("p.y");
    private static final NumericTerm.FromOnePosition Z = position("p.z");

    private static NumericTerm.FromOnePosition position(String path) {
        return new NumericTerm.ValueOf(TermPath.of(path));
    }

    /** Every position of the form, read and written on the whole numbers. */
    private static Map<NumericTerm, TermOrders> wholeNumbers() {
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        for (NumericTerm.FromOnePosition each : java.util.List.of(X, Y, Z)) {
            on.put(each, TermOrdersFixtures.itself(each, new Carrier.Whole()));
        }
        return on;
    }

    private static Realization realizedAt(int level, SearchRegion within) {
        Standing standing = new BorderQuantity.OverAForm("decide",
                new LinearForm<NumericTerm>(ExactRatio.ZERO,
                        Map.of(X, ExactRatio.ONE, Y, ExactRatio.ONE, Z, ExactRatio.ONE)),
                wholeNumbers())
                .standingAt(new Criterion.AtTheLevel(Level.OfTheQuantity.of(level)));
        return new LevelRealizer().realize(standing, within,
                NothingTheDeclarationsRefuse.at(TermPath.of("p.x"), TermPath.of("p.y"),
                        TermPath.of("p.z")));
    }

    /**
     * {@code x + y + z = 6}, each from nought to ten: the first value of {@code x} is nought, of
     * {@code y} nought, and {@code z} is six. The rules are read for the assignment and for none of
     * the positions fixed on the way.
     */
    @Test
    void theRulesAreReadOnceForTheAssignmentAndNotForEachPositionFixed() {
        Counting region = new Counting(new Counts());

        Realization found = realizedAt(6, region);

        assertEquals(Map.of(RealizationTarget.of(X), new Count(BigDecimal.ZERO),
                        RealizationTarget.of(Y), new Count(BigDecimal.ZERO),
                        RealizationTarget.of(Z), new Count(BigDecimal.valueOf(6))),
                assertInstanceOf(Realization.Found.class, found).fixing(),
                "the first value of each position, and the last solved");
        assertEquals("emptiness=5 fixed=2",
                "emptiness=" + region.counts.emptiness.get() + " fixed=" + region.counts.fixed.get(),
                "the item's own readings around the search and the one of the assignment; the"
                        + " walk adds one of each for every position it fixes before the last,"
                        + " which is two here");
    }

    /**
     * And where the rules refuse the first assignment, the walk finds the next one as it would
     * have: {@code x} at nought is refused, so the walk fixes {@code x} at one, {@code y} at nought
     * and solves {@code z} at five.
     */
    @Test
    void anAssignmentTheRulesRefuseLeavesTheWalkToFindTheNext() {
        Counting region = new Counting(new Counts(), Map.of(), true);

        Realization found = realizedAt(6, region);

        assertEquals(Map.of(RealizationTarget.of(X), new Count(BigDecimal.ONE),
                        RealizationTarget.of(Y), new Count(BigDecimal.ZERO),
                        RealizationTarget.of(Z), new Count(BigDecimal.valueOf(5))),
                assertInstanceOf(Realization.Found.class, found).fixing());
    }

    /** What the search reads and fixes, shared by every region it narrows to. */
    private static final class Counts {
        final AtomicInteger emptiness = new AtomicInteger();
        final AtomicInteger fixed = new AtomicInteger();
    }

    /**
     * A region that runs every position from nought to ten and narrows nothing, counting. Where it
     * refuses {@code x} at nought, it says so once a position is fixed there.
     */
    private record Counting(Counts counts, Map<NumericTerm, Place> standing,
                            boolean refusesXAtNought) implements SearchRegion {

        Counting(Counts counts) {
            this(counts, Map.of(), false);
        }

        private static final NumericDomain.Bounds ZERO_TO_TEN = new NumericDomain.Bounds(
                Endpoint.inclusive(new Count(BigDecimal.ZERO)),
                Endpoint.inclusive(new Count(BigDecimal.TEN)));

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
            counts.fixed.incrementAndGet();
            Map<NumericTerm, Place> both = new LinkedHashMap<>(standing);
            both.putAll(fixed);
            return new Counting(counts, both, refusesXAtNought);
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
            return new NumericDomain.FormProjection.Within(ZERO_TO_TEN);
        }

        @Override
        public Optional<EmptyInput> emptiness() {
            counts.emptiness.incrementAndGet();
            return refusesXAtNought && new Count(BigDecimal.ZERO).equals(standing.get(X))
                    ? Optional.of(new EmptyInput.ProvedByTheDeclarations(
                            new Emptiness.ConflictingRules()))
                    : Optional.empty();
        }
    }
}
