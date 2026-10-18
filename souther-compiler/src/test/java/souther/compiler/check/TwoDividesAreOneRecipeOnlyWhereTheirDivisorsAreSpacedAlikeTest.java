package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two divides are one recipe only where their divisors' values are spaced alike, as well as running
 * between the same ends.
 *
 * <p>The spacing decides what a divide by a range holding nought comes to: by whole numbers it is
 * read on each side of nought, and by a dense order it is not read at all. Two recipes that agree on
 * every form and on the ends of the divisor's extent and differ in its spacing are two values, and
 * filed under one atom, what the atom means would turn on which of them named it.
 */
class TwoDividesAreOneRecipeOnlyWhereTheirDivisorsAreSpacedAlikeTest {

    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");

    private static final LinearForm<FactSubject> DIVIDEND =
            LinearForm.atom(AsPlaces.of(new BindingId(OWNER, 1)));

    private static final LinearForm<FactSubject> DIVISOR =
            LinearForm.atom(AsPlaces.of(new BindingId(OWNER, 2)));

    private static Derivation dividing(String low, String high, Granularity spacing) {
        Bounds within = new Bounds(Endpoint.inclusive(Count.of(new BigDecimal(low))),
                Endpoint.inclusive(Count.of(new BigDecimal(high))));
        return new Derivation.TruncatingQuotient(DIVIDEND, DIVISOR,
                new Derivation.DivisorExtent(within, spacing));
    }

    @Test
    void divisorsSpacedDifferentlyAreTwoRecipes() {
        assertFalse(Terms.sameDerivation(dividing("-5", "5", Granularity.DISCRETE),
                dividing("-5", "5", Granularity.DENSE)));
    }

    /** The control: the same spacing over the same ends is one recipe, and an end written to more
     * places is the same end. */
    @Test
    void divisorsSpacedAlikeOverTheSameEndsAreOneRecipe() {
        assertTrue(Terms.sameDerivation(dividing("-5", "5", Granularity.DISCRETE),
                dividing("-5", "5", Granularity.DISCRETE)));
        assertTrue(Terms.sameDerivation(dividing("-5", "5", Granularity.DENSE),
                dividing("-5.00", "5.0", Granularity.DENSE)));
        assertFalse(Terms.sameDerivation(dividing("-5", "5", Granularity.DENSE),
                dividing("-5", "6", Granularity.DENSE)));
    }
}
