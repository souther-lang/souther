package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An element of a list a total is the sum of is written through
 * {@code DecimalPoints.writtenForARow}, and through nothing else.
 *
 * <p>The places a row is built at are the generation's budget: which lists are tried, and not
 * which decimals there are. The builder holds to it only because every number it derives for an
 * element (a share of what is owed, a number moved from the start) is written there. A direct
 * {@code ExactRatio.writtenDecimal} in the builder, named as a call or as a reference, is an element
 * whose places nothing bounds, and the budget would no longer be what bounds the lists built.
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
