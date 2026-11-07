package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a fork turns on is a set of positions, so two readings of one input that found them in
 * two orders have found one thing.
 *
 * <p>The positions are read off the numbers of a condition, and those are held in whatever order
 * the arithmetic put them. An answer that kept that order would be unequal to itself from one
 * compilation to the next, and nothing about equality could repair it.
 */
class AForkTurnsOnTheSamePositionsWhateverOrderTheyWereReadInTest {

    private static final TermPath PRICE = TermPath.of("price");

    private static final TermPath QUANTITY = TermPath.of("quantity");

    @Test
    void twoReadingsOfTheSamePositionsAreOneDependency() {
        ForkDependencies.Dependency.Known forward =
                new ForkDependencies.Dependency.Known(List.of(PRICE, QUANTITY));
        ForkDependencies.Dependency.Known backward =
                new ForkDependencies.Dependency.Known(List.of(QUANTITY, PRICE));

        assertEquals(forward, backward);
        assertEquals(forward.positions(), backward.positions());
    }
}
