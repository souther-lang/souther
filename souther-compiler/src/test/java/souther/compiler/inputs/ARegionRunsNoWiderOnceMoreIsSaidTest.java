package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.NumericDomain;

import java.math.BigInteger;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Saying more of a region leaves every position a run no wider, and a class no wider.
 *
 * <p>What {@link SearchRegion#runsOnlyNarrowWhenFixed} promises, held against the regions a model
 * reads. A search that takes the first value of each position from where it runs before anything is
 * fixed, and not from where it runs once the positions before it are, gets the value the walk
 * would take only if the narrower run lies inside the wider one: the first value of the wider run
 * that lies in the narrower is then the first of that. The ranges and the classes are what the
 * region approximates, so this is the approximation held to narrowing, and not the sets of values
 * they stand for.
 *
 * <p>Regions are written at random over five numbers, one held to the even ones and one to the
 * multiples of a thousand, by relations taken in and numbers fixed, and each is set beside the one
 * before it. A region left with nothing is nowhere for any position to run, and what is said beside
 * it leaves it that.
 */
class ARegionRunsNoWiderOnceMoreIsSaidTest {

    private static final int REGIONS = 500;

    @Test
    void everyPositionRunsNoWiderOnceMoreIsSaid() {
        Random random = new Random(2984);
        int narrower = 0;
        int compared = 0;
        for (int i = 0; i < REGIONS; i++) {
            SearchRegion coarser = RegionsRefinedAtRandom.region();
            StringBuilder said = new StringBuilder();
            for (int step = 0, steps = 1 + random.nextInt(5); step < steps; step++) {
                int saidSoFar = said.length();
                SearchRegion finer = RegionsRefinedAtRandom.refined(coarser, random, said);
                String lastSaid = said.substring(saidSoFar);
                String allSaid = said.toString();
                if (coarser.emptiness().isPresent() || finer.emptiness().isPresent()) {
                    coarser = finer;
                    continue;
                }
                for (String name : RegionsRefinedAtRandom.NAMES) {
                    NumericTerm term = RegionsRefinedAtRandom.term(name);
                    NumericDomain.FormProjection before = coarser.projectionOf(term);
                    NumericDomain.FormProjection after = finer.projectionOf(term);
                    compared++;
                    if (before instanceof NumericDomain.FormProjection.NothingIsLeft) {
                        assertTrue(after instanceof NumericDomain.FormProjection.NothingIsLeft,
                                () -> name + " has somewhere to run in a region made from one that"
                                        + " leaves nowhere: " + after);
                    } else if (before instanceof NumericDomain.FormProjection.Within wider
                            && after instanceof NumericDomain.FormProjection.Within narrow) {
                        assertTrue(narrow.bounds().liesWithin(wider.bounds()),
                                () -> name + " runs " + narrow.bounds() + " in a region made from"
                                        + " one where it ran " + wider.bounds() + "; said"
                                        + allSaid + "; last" + lastSaid);
                        if (!narrow.bounds().equals(wider.bounds())) {
                            narrower++;
                        }
                    }
                }
                coarser = finer;
            }
        }
        assertTrue(compared > REGIONS, "runs compared: " + compared);
        assertTrue(narrower > REGIONS / 4, "and of them, those that were narrowed: " + narrower);
    }

    /**
     * The class a number is held to is the declarations' and what the remainders fixed beside it
     * leave, so nothing said here by fixing a number or taking a relation in widens it. It is
     * narrowed by a remainder fixed, which this model's numbers do not have.
     */
    @Test
    void everyClassIsNoWiderOnceMoreIsSaid() {
        Random random = new Random(2985);
        long[] values = {-3, -1, 0, 1, 2, 3, 7, 10, 20, 21, 500, 1000, 1500, 2000, 5000, 6000};
        int members = 0;
        for (int i = 0; i < REGIONS; i++) {
            SearchRegion coarser = RegionsRefinedAtRandom.region();
            for (int step = 0, steps = 1 + random.nextInt(5); step < steps; step++) {
                SearchRegion finer = RegionsRefinedAtRandom.refined(coarser, random);
                for (String name : RegionsRefinedAtRandom.NAMES) {
                    NumericTerm.ValueOf term = RegionsRefinedAtRandom.term(name);
                    for (long value : values) {
                        BigInteger whole = BigInteger.valueOf(value);
                        if (finer.classAt(term).holds(whole)) {
                            members++;
                            assertTrue(coarser.classAt(term).holds(whole),
                                    () -> name + " may be " + whole + " in a region made from one"
                                            + " where its class has no such member");
                        }
                    }
                }
                coarser = finer;
            }
        }
        assertTrue(members > REGIONS, "members of a class compared: " + members);
    }
}
