package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What every {@code Int} holds is a bound on a value an input holds as one, and on nothing the
 * arithmetic of such values works out: an ordering both ends of an {@code Int} meet is held of the
 * value, and is not of the product of two, which passes the ends though each factor lies between
 * them. A number that is not an {@code Int} is held by what its declarations say alone.
 */
class AnIntsEndsBoundOnlyAValueReadOffAnInputTest {

    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("a"));
    private static final NumericTerm B = new NumericTerm.ValueOf(TermPath.of("b"));

    /** Nothing declared, and the values named here read as {@code Int}. */
    private record Reading(boolean ints) implements SearchRegion {

        @Override
        public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
            return NothingTheRulesSay.REGION.assuming(form, rel);
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
            return new NumericDomain.FormProjection.Within(NumericDomain.Bounds.OPEN);
        }

        @Override
        public Optional<EmptyInput> emptiness() {
            return Optional.empty();
        }

        @Override
        public boolean isAnInt(NumericTerm term) {
            return ints && !(term instanceof NumericTerm.ProductOf);
        }
    }

    /** {@code term + constant rel 0}. */
    private static boolean held(NumericTerm term, BigInteger constant, Rel rel, boolean ints) {
        LinearForm<NumericTerm> form = new LinearForm<>(
                ExactRatio.of(constant),
                Map.of(term, ExactRatio.of(BigInteger.ONE)));
        return TakenConstraint.holdsOverTheRunsOf(form, rel, new Reading(ints));
    }

    /** {@code term >= least}: {@code term - least >= 0}. */
    private static boolean atLeastTheLeast(NumericTerm term, boolean ints) {
        return held(term, BigInteger.valueOf(Long.MIN_VALUE).negate(), Rel.GE, ints);
    }

    /** {@code term <= greatest}: {@code term - greatest <= 0}. */
    private static boolean atMostTheGreatest(NumericTerm term, boolean ints) {
        return held(term, BigInteger.valueOf(Long.MAX_VALUE).negate(), Rel.LE, ints);
    }

    @Test
    void aValueAnIntHoldsLiesBetweenTheEnds() {
        assertEquals(true, atLeastTheLeast(A, true));
        assertEquals(true, atMostTheGreatest(A, true));
    }

    @Test
    void aNumberThatIsNoIntIsHeldByNothingButItsDeclarations() {
        assertEquals(false, atLeastTheLeast(A, false));
        assertEquals(false, atMostTheGreatest(A, false));
    }

    @Test
    void theProductOfTwoIntsIsAsWideAsTheRangesOfItsFactorsWorkOutTo() {
        NumericTerm product = NumericTerm.ProductOf.of(LinearForm.atom(A), LinearForm.atom(B));
        assertEquals(false, atLeastTheLeast(product, true));
        assertEquals(false, atMostTheGreatest(product, true));
    }
}
