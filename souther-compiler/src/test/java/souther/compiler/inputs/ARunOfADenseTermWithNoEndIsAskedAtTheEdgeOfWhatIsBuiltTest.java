package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Term;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Where nothing can stop a row, a run of a dense term with no end on a side is still asked at the
 * edge of what is built ({@link DecimalPoints#edgeOfWhatIsBuilt}): the rows there are what shows
 * the run, and a term whose order stops short of the edge has none there.
 */
class ARunOfADenseTermWithNoEndIsAskedAtTheEdgeOfWhatIsBuiltTest {

    /** {@code a - s - 5 >= 0}, both from nought and {@code a} counted on {@code aRunsTo}. */
    private static Leaves leftOfAmounts(NumericDomain.Bounds aRunsTo) {
        NumericDomain.Bounds amounts = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(0)), null);
        List<Term<String>> terms = List.of(
                new Term<>(List.of("a"), ExactRatio.ONE, amounts, amounts, null, true,
                        Granularity.DENSE, aRunsTo, "a"),
                new Term<>(List.of("s"), ExactRatio.of(-1), amounts, amounts, null, true,
                        Granularity.DENSE, NumericDomain.Bounds.OPEN, "s"));
        return WhatARelationLeavesUndivided.leavesOf(terms, 0, ExactRatio.of(-5), Rel.GE,
                String::equals, (one, other) -> true, Granularity.DENSE, null, List.of(),
                new Operations(List.of(), Told.EVERY));
    }

    @Test
    void aTermWhoseOrderStopsShortOfTheEdgeHasNoRowThere() {
        assertNull(leftOfAmounts(new NumericDomain.Bounds(null,
                Endpoint.inclusive(Count.of(BigDecimal.TEN.pow(100))))));
    }

    @Test
    void aTermReachingTheEdgeIsShownAsTheRunItIs() {
        Leaves.Settled open = assertInstanceOf(Leaves.Settled.class,
                leftOfAmounts(NumericDomain.Bounds.OPEN));
        assertEquals(1, open.runs().size());
        assertFalse(open.runs().getFirst().holds());
    }
}
