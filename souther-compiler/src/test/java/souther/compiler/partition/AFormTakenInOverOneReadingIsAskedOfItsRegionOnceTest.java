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

import java.util.Map;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a region takes a form in coming out a way is asked of it once, and what is kept is its
 * answer: nothing where it takes it in, and its word for why not where it does not.
 */
class AFormTakenInOverOneReadingIsAskedOfItsRegionOnceTest {

    private static final NumericTerm.FromOnePosition NAMED =
            new NumericTerm.ValueOf(TermPath.of("named"));
    private static final NumericTerm.FromOnePosition SPACED =
            new NumericTerm.ValueOf(TermPath.of("spaced"));

    /** A region that takes in every form over {@code SPACED} and refuses any over {@code NAMED},
     *  counting what it is asked. */
    private record Counting(AtomicInteger asked) implements SearchRegion {

        @Override
        public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
            asked.incrementAndGet();
            return form.coefs().containsKey(NAMED)
                    ? new Assumption.Refused(new Refusal.NoOrderUnderATerm(NAMED))
                    : new Assumption.Taken(this);
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

    @Test
    void aFormTakenInAndAFormRefusedAreEachAskedOnceAndAnsweredAsTheRegionAnswered() {
        AtomicInteger asked = new AtomicInteger();
        FormsTakenIn forms = new FormsTakenIn(new Counting(asked));

        for (int again = 0; again < 3; again++) {
            assertTrue(forms.refusalOf(over(SPACED, 0), Rel.LE).isEmpty());
            assertEquals(Optional.of(new SearchRegion.Refusal.NoOrderUnderATerm(NAMED)),
                    forms.refusalOf(over(NAMED, 0), Rel.LE));
        }
        assertEquals(2, asked.get());
    }

    @Test
    void aDifferentWayOrAFormIsAskedAgain() {
        AtomicInteger asked = new AtomicInteger();
        FormsTakenIn forms = new FormsTakenIn(new Counting(asked));

        forms.refusalOf(over(SPACED, 0), Rel.LE);
        forms.refusalOf(over(SPACED, 0), Rel.GE);
        forms.refusalOf(over(SPACED, 5), Rel.LE);
        assertEquals(3, asked.get());
    }

    private static LinearForm<NumericTerm> over(NumericTerm term, long constant) {
        return new LinearForm<>(ExactRatio.of(constant), Map.of(term, ExactRatio.ONE));
    }
}
