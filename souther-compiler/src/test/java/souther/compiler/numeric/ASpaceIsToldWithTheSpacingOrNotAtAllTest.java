package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
 *
 * <p>Where the ends of an order are not told, which is a thing a reader says of an atom it found no
 * type for, the atom is not read as having none: a system it is in is not shown to leave no row.
 */
class ASpaceIsToldWithTheSpacingOrNotAtAllTest {

    private static final long GREATEST = Long.MAX_VALUE;

    private static final NumericDomain.Bounds AN_INT_STOPS = new NumericDomain.Bounds(
            Endpoint.inclusive(Count.of(Long.MIN_VALUE)), Endpoint.inclusive(Count.of(GREATEST)));

    private static final NumberSpace AN_INT =
            NumberSpace.stopping(Granularity.DISCRETE, AN_INT_STOPS);

    private static final NumberSpace SPACED_ONLY = NumberSpace.spacedOnly(Granularity.DISCRETE);

    private static final NumberSpace ENDLESS =
            NumberSpace.stopping(Granularity.DENSE, NumericDomain.Bounds.OPEN);

    private static LinearForm<String> differenceAtLeast(long atLeast) {
        return LinearForm.<String>atom("a")
                .minus(LinearForm.atom("b")).orNull()
                .minus(LinearForm.constant(ExactRatio.of(atLeast))).orNull();
    }

    private static NumericDomain<String> bAboveAndTheDifferenceAtTheEnd(
            NumberSpace space, long atLeast, long theSmallestB) {
        Map<String, NumberSpace> spaces = Map.of("a", space, "b", space);
        return NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .assume(LinearForm.atomMinusConstant("b", ExactRatio.of(theSmallestB)),
                        Rel.GE, spaces)
                .assume(differenceAtLeast(atLeast), Rel.GE, spaces);
    }

    @Test
    void theRulesLeaveAPointAndTheTypeLeavesNoRow() {
        NumericDomain<String> past = bAboveAndTheDifferenceAtTheEnd(AN_INT, GREATEST, 1);
        assertFalse(past.isBottom(), "the rules alone are satisfiable");
        assertTrue(past.leavesNoRow(), "no value of the type satisfies them");
    }

    @Test
    void aNeighbourThatStaysInsideTheTypeLeavesARow() {
        assertFalse(bAboveAndTheDifferenceAtTheEnd(AN_INT, GREATEST - 1, 1).leavesNoRow());
        assertFalse(bAboveAndTheDifferenceAtTheEnd(AN_INT, GREATEST, 0).leavesNoRow());
    }

    @Test
    void theSpaceIsKeptWhenTheNamesChange() {
        NumericDomain<String> renamed = bAboveAndTheDifferenceAtTheEnd(AN_INT, GREATEST, 1)
                .over(name -> name + "'", CanonicalOrder.asTheyAreSpelled());
        assertTrue(renamed.leavesNoRow());
    }

    @Test
    void theSpaceIsKeptWhenTwoReadingsMeet() {
        NumericDomain<String> met = NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .meet(bAboveAndTheDifferenceAtTheEnd(AN_INT, GREATEST, 1));
        assertTrue(met.leavesNoRow());
    }

    @Test
    void anEndlessOrderIsSomethingATypeSaysAndLeavesARow() {
        assertFalse(bAboveAndTheDifferenceAtTheEnd(ENDLESS, GREATEST, 1).leavesNoRow());
    }

    @Test
    void anOrderWhoseEndsWereNeverToldIsNotReadAsOneThatHasNone() {
        NumericDomain<String> untold = bAboveAndTheDifferenceAtTheEnd(SPACED_ONLY, GREATEST, 1);
        assertFalse(untold.isBottom());
        assertFalse(untold.leavesNoRow(), "nothing says the rules' point is past the type");
    }

    @Test
    void endsToldAfterTheRulesAreTheEndsAnAtomHasFromThenOn() {
        NumericDomain<String> untold = bAboveAndTheDifferenceAtTheEnd(SPACED_ONLY, GREATEST, 1);
        NumericDomain<String> told = untold.told(Map.of("a", AN_INT, "b", AN_INT));
        assertTrue(told.leavesNoRow());
        assertEquals(AN_INT, told.spaceOf("a"));
        assertFalse(untold.leavesNoRow(), "the domain it was told from is not changed");
    }

    @Test
    void anAtomOnlyToldOfIsOneTheDomainHasSpokenOf() {
        NumericDomain<String> top = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
        assertFalse(top.atomsSpokenOf().contains("a"));
        assertTrue(top.told(Map.of("a", AN_INT)).atomsSpokenOf().contains("a"));
    }

    @Test
    void anAtomWithNoSpaceToldIsRefusedAndNotReadAsEndless() {
        assertThrows(IllegalStateException.class, () ->
                NumericDomain.top(CanonicalOrder.asTheyAreSpelled()).assume(
                        LinearForm.atomMinusConstant("a", ExactRatio.ONE), Rel.GE, Map.of()));
    }

    @Test
    void oneAtomToldTwoDifferentEndsIsRefused() {
        NumericDomain<String> told = NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .told(Map.of("a", AN_INT));
        assertThrows(IllegalStateException.class, () -> told.told(Map.of("a",
                NumberSpace.stopping(Granularity.DISCRETE, NumericDomain.Bounds.OPEN))));
    }

    @Test
    void oneAtomToldTwoDifferentSpacingsIsRefused() {
        NumericDomain<String> told = NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .told(Map.of("a", AN_INT));
        assertThrows(IllegalStateException.class,
                () -> told.told(Map.of("a", NumberSpace.spacedOnly(Granularity.DENSE))));
    }

    @Test
    void anAtomToldTheSameThingAgainChangesNothing() {
        NumericDomain<String> told = NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .told(Map.of("a", AN_INT));
        assertTrue(told == told.told(Map.of("a", AN_INT)));
        assertTrue(told == told.told(Map.of("a", SPACED_ONLY)),
                "saying less than is known adds nothing");
    }
}
