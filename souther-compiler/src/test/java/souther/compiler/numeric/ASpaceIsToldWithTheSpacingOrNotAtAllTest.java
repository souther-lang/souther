package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a type says of an atom — how its values are spaced and where its order stops — is told to a
 * domain as one value, and what the domain answers about the rows is the same through every
 * operation that carries it.
 *
 * <p>{@code b >= 1} beside {@code a - b >= M}, with {@code M} the greatest whole number the type
 * holds, has a solution over the integers and none inside the type. The rules leave a point
 * ({@link NumericDomain#isBottom} is false) and a row is nowhere
 * ({@link NumericDomain#leavesNoRow}), and the two answers are asked apart so that neither is read
 * as the other.
 */
class ASpaceIsToldWithTheSpacingOrNotAtAllTest {

    private static final long GREATEST = Long.MAX_VALUE;

    private static final NumberSpace A_LONG = new NumberSpace(Granularity.DISCRETE,
            new NumericDomain.Bounds(Endpoint.inclusive(Count.of(Long.MIN_VALUE)),
                    Endpoint.inclusive(Count.of(GREATEST))));

    private static final NumberSpace ENDLESS =
            new NumberSpace(Granularity.DENSE, NumericDomain.Bounds.OPEN);

    private static NumericDomain<String> bAboveOneAndTheDifferenceAtTheEnd(long atLeast,
                                                                           long theSmallestB) {
        Map<String, NumberSpace> spaces = Map.of("a", A_LONG, "b", A_LONG);
        LinearForm<String> difference = LinearForm.<String>atom("a")
                .minus(LinearForm.atom("b")).orNull()
                .minus(LinearForm.constant(ExactRatio.of(atLeast))).orNull();
        return NumericDomain.top(CanonicalOrder.<String>asTheyAreSpelled())
                .assumeWithin(LinearForm.atomMinusConstant("b", ExactRatio.of(theSmallestB)),
                        Rel.GE, spaces)
                .assumeWithin(difference, Rel.GE, spaces);
    }

    @Test
    void theRulesLeaveAPointAndTheTypeLeavesNoRow() {
        NumericDomain<String> past = bAboveOneAndTheDifferenceAtTheEnd(GREATEST, 1);
        assertFalse(past.isBottom(), "the rules alone are satisfiable");
        assertTrue(past.leavesNoRow(), "no value of the type satisfies them");
    }

    @Test
    void aNeighbourThatStaysInsideTheTypeLeavesARow() {
        assertFalse(bAboveOneAndTheDifferenceAtTheEnd(GREATEST - 1, 1).leavesNoRow());
        assertFalse(bAboveOneAndTheDifferenceAtTheEnd(GREATEST, 0).leavesNoRow());
    }

    @Test
    void theSpaceIsKeptWhenTheNamesChange() {
        NumericDomain<String> renamed = bAboveOneAndTheDifferenceAtTheEnd(GREATEST, 1)
                .over(name -> name + "'", CanonicalOrder.<String>asTheyAreSpelled());
        assertTrue(renamed.leavesNoRow());
    }

    @Test
    void theSpaceIsKeptWhenTwoReadingsMeet() {
        NumericDomain<String> met = NumericDomain.<String>top(CanonicalOrder.asTheyAreSpelled())
                .meet(bAboveOneAndTheDifferenceAtTheEnd(GREATEST, 1));
        assertTrue(met.leavesNoRow());
    }

    @Test
    void anEndlessOrderIsSomethingATypeSaysAndLeavesARow() {
        Map<String, NumberSpace> spaces = Map.of("a", ENDLESS, "b", ENDLESS);
        LinearForm<String> difference = LinearForm.<String>atom("a")
                .minus(LinearForm.atom("b")).orNull()
                .minus(LinearForm.constant(ExactRatio.of(GREATEST))).orNull();
        NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.<String>asTheyAreSpelled())
                .assumeWithin(LinearForm.atomMinusConstant("b", ExactRatio.ONE), Rel.GE, spaces)
                .assumeWithin(difference, Rel.GE, spaces);
        assertFalse(domain.leavesNoRow());
    }

    @Test
    void anAtomWithNoSpaceToldIsRefusedAndNotReadAsEndless() {
        assertThrows(IllegalStateException.class, () ->
                NumericDomain.top(CanonicalOrder.<String>asTheyAreSpelled()).assumeWithin(
                        LinearForm.atomMinusConstant("a", ExactRatio.ONE), Rel.GE, Map.of()));
    }

    @Test
    void oneAtomToldTwoDifferentOrdersIsRefused() {
        NumericDomain<String> told = NumericDomain.top(CanonicalOrder.<String>asTheyAreSpelled())
                .assumeWithin(LinearForm.atomMinusConstant("a", ExactRatio.ONE), Rel.GE,
                        Map.of("a", A_LONG));
        assertThrows(IllegalStateException.class, () -> told.assumeWithin(
                LinearForm.atomMinusConstant("a", ExactRatio.ONE), Rel.GE,
                Map.of("a", new NumberSpace(Granularity.DISCRETE, NumericDomain.Bounds.OPEN))));
    }
}
