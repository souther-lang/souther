package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An element of a list a total is the sum of is written through
 * {@code DecimalOperation.writtenForARow}, and through nothing else.
 *
 * <p>What the analysis shows of an operation worked out of a total takes the scale of the total
 * to be no more than the places a row is built at, and that is true of the lists that are built
 * only because every number the builder derives for an element is written there. It derives them
 * (a share of what is owed, a number moved from the start), so they are no number the analysis
 * chose and filtered. A direct {@code ExactRatio.writtenDecimal} in the builder, named as a call or
 * as a reference, is an element whose places nothing bounds, and a claim made of the rows built
 * would no longer be a claim of the rows that are.
 */
class ADecimalAListIsBuiltWithIsWrittenThroughTheOneThatBoundsItsPlacesTest {

    private static final String BUILDER = "souther.compiler.partition.ContainersAddingUp";

    @Test
    void theBuilderOfTheListsWritesNoDecimalDirectly() {
        List<String> direct = new ArrayList<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (site.owner().equals("souther.compiler.numeric.ExactRatio")
                    && site.member().equals("writtenDecimal")
                    && site.from().startsWith(BUILDER)) {
                direct.add(site.from() + "#" + site.method() + " " + site.how());
            }
        }
        assertEquals(List.of(), direct);
    }
}
