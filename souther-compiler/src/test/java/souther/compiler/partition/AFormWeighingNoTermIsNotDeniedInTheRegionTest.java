package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.SearchRegion;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.lang.reflect.Proxy;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A case that states a relation over no number is left out of the region, which is not asked to
 * take it in: a region refuses a form weighing no term, since there is no constraint in it.
 *
 * <p>The region here answers nothing. Reaching it at all is the failure, so that what is held is
 * that the case is passed over before the region is asked.
 */
class AFormWeighingNoTermIsNotDeniedInTheRegionTest {

    private static SearchRegion aRegionNothingMayAsk() {
        return (SearchRegion) Proxy.newProxyInstance(SearchRegion.class.getClassLoader(),
                new Class<?>[] {SearchRegion.class}, (proxy, method, args) -> {
                    throw new AssertionError("the region was asked " + method.getName());
                });
    }

    @Test
    void aRelationOverNoNumberLeavesTheRegionAsItWas() {
        Proposition aConstant = new Proposition.Compared(
                new Relation.Affine(new LinearForm<Quantity>(ExactRatio.ONE, Map.of()), Rel.GE),
                true);
        SearchRegion region = aRegionNothingMayAsk();

        assertSame(region, OutsideTheOtherReadings.of(List.of(aConstant)).apply(region));
    }
}
