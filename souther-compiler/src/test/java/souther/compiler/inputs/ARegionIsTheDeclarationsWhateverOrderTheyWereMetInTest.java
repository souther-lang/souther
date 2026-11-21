package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.observe.ObservedValue;

import java.math.BigInteger;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two readings of one rule that declare the same bounds, met in another order, are one region,
 * and how far out a bound goes, shown of that region by either, stands of it together.
 */
class ARegionIsTheDeclarationsWhateverOrderTheyWereMetInTest {

    private static final ABoundThatKeepsEveryRunGoing.Held OPEN =
            new ABoundThatKeepsEveryRunGoing.Held(null, null);

    private static ABoundThatKeepsEveryRunGoing on(String parameter, boolean atMost, long at) {
        return new ABoundThatKeepsEveryRunGoing(
                new ABoundThatKeepsEveryRunGoing.Holder.AParameter(parameter, "Int"), atMost,
                BigInteger.valueOf(at), new ObservedValue.Integer(at), OPEN);
    }

    /** Readings put together in any order come to one region, and a value holding all of it at
     *  once is shown wherever one reading showed it of everything the region declares on, put in
     *  first or last — and nowhere none did. */
    @Test
    void readingsPutTogetherInAnyOrderComeToOneRegion() {
        ABoundThatKeepsEveryRunGoing x = on("x", true, 10);
        ABoundThatKeepsEveryRunGoing y = on("y", true, 20);
        WhatKeepsEveryRunGoing ofX = WhatKeepsEveryRunGoing.of(List.of(x)).orElseThrow();
        WhatKeepsEveryRunGoing ofY = WhatKeepsEveryRunGoing.of(List.of(y)).orElseThrow();
        WhatKeepsEveryRunGoing ofBoth = WhatKeepsEveryRunGoing.of(List.of(x, y)).orElseThrow();

        for (List<WhatKeepsEveryRunGoing> order : List.of(List.of(ofX, ofY, ofBoth),
                List.of(ofX, ofBoth, ofY), List.of(ofY, ofX, ofBoth), List.of(ofY, ofBoth, ofX),
                List.of(ofBoth, ofX, ofY), List.of(ofBoth, ofY, ofX))) {
            Optional<WhatKeepsEveryRunGoing> region = Optional.of(order.getFirst());
            for (WhatKeepsEveryRunGoing each : order.subList(1, 3)) {
                region = WhatKeepsEveryRunGoing.together(region, Optional.of(each));
            }
            assertEquals(Set.of(x, y), region.orElseThrow().bounds(), order.toString());
            assertTrue(region.orElseThrow().heldTogether(), order.toString());
        }
        assertFalse(WhatKeepsEveryRunGoing.together(Optional.of(ofX), Optional.of(ofY))
                .orElseThrow().heldTogether());
    }

    @Test
    void howFarOutABoundGoesStandsOfTheSameDeclarationsMetInAnotherOrder() {
        ABoundThatKeepsEveryRunGoing x = on("x", true, 10);
        ABoundThatKeepsEveryRunGoing y = on("y", false, 0);
        WhatKeepsEveryRunGoing one = WhatKeepsEveryRunGoing.of(List.of(x, y)).orElseThrow();
        WhatKeepsEveryRunGoing other = WhatKeepsEveryRunGoing.of(List.of(y, x)).orElseThrow()
                .asFarOutAsCanBe(Set.of(x));

        assertEquals(Set.of(x), WhatKeepsEveryRunGoing.together(Optional.of(one),
                Optional.of(other)).orElseThrow().asFarOutAsCanBe());
    }
}
