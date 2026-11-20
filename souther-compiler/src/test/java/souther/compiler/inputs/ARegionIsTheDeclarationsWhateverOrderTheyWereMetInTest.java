package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.observe.ObservedValue;

import java.math.BigInteger;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two readings of one rule that declare the same bounds, met in another order, are one region,
 * and how far out a bound goes, shown of that region by either, stands of it together.
 */
class ARegionIsTheDeclarationsWhateverOrderTheyWereMetInTest {

    private static final ABoundThatKeepsEveryRunGoing.Held OPEN =
            new ABoundThatKeepsEveryRunGoing.Held(null, null);

    private static ABoundThatKeepsEveryRunGoing on(String field, boolean atMost, long at) {
        return new ABoundThatKeepsEveryRunGoing(
                new ABoundThatKeepsEveryRunGoing.Holder.AData("P", field), atMost,
                BigInteger.valueOf(at), new ObservedValue.Integer(at), OPEN);
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
