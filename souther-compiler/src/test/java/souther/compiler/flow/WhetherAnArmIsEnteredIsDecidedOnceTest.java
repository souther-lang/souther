package souther.compiler.flow;

import org.junit.jupiter.api.Test;
import souther.compiler.WhatWasCompiled;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Whether a run can enter an arm of a fork is decided once, where the fork is settled, and read
 * from there.
 *
 * <p>Two answers can be given to it: what the condition states, where the reading has that in
 * hand ({@link ComparisonWays#stated}), and what the parts of the condition come to in the tree
 * being read ({@link Comes#mayCome}). The first is what the condition means and the second is
 * what is left where nothing states it, so the two are weighed in one place and every reader asks
 * that place ({@link ValueArrivals#mayEnter}). A reader that asked the parts itself would enter an
 * arm the condition's meaning closes: a condition written as an operation the tree expands would
 * open an arm that the same condition written as a comparison keeps closed.
 */
class WhetherAnArmIsEnteredIsDecidedOnceTest {

    @Test
    void onlyTheSettlingOfAForkWeighsWhatItsConditionStatesAgainstItsParts() {
        assertEquals(Set.of("souther.compiler.flow.ValueArrivals"),
                WhatWasCompiled.callersOf(Comes.class, "mayCome"),
                "what the parts of a condition come to is read where a fork is settled, beside"
                        + " what the condition states, and nowhere else");
        assertEquals(Set.of("souther.compiler.flow.ValueArrivals"),
                WhatWasCompiled.callersOf(ComparisonWays.class, "stated"),
                "and what a fork's condition states is asked there too");
    }
}
