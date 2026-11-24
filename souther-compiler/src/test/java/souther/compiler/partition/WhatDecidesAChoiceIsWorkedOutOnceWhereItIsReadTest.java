package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run works out to decide a choice is worked out once for each place the choice is read
 * in, and not once for every comparison read through it.
 *
 * <p>A value chosen by an {@code if} and carried on into the next one is read through by every
 * comparison after it, on every arm before it, and by each rule tried on each. Which arm a run
 * takes there turns on the choice and on where its names are read, so the comparisons and the
 * rules ask the same question again, and the work is what the distinct questions come to.
 */
class WhatDecidesAChoiceIsWorkedOutOnceWhereItIsReadTest {

    private static final String CHAIN = """
            module m

            let atMost (wanted: Int, held: Int): Int =
                if wanted < held then wanted else held

            behavior paid : (sum: Int, a: Int, b: Int, c: Int) -> Bool
            let paid (sum, a, b, c) = {
                let first = atMost(sum, a)
                let left1 = sum - first
                let second = atMost(left1, b)
                let left2 = left1 - second
                let third = atMost(left2, c)
                guard third >= 0 && third <= c
                    else unreachable "it is between nought and what is held"
                left2 - third == 0
            }
            """;

    @Test
    void mostAskingsAreAnsweredFromWhatWasWorkedOutBefore() {
        long[] counting = {0, 0};
        AffineReading.DECIDED = counting;
        try {
            ACompiledModel.measured(CHAIN, new Adequacy.Asked(Adequacy.Level.OFF, false));
        } finally {
            AffineReading.DECIDED = null;
        }
        long asked = counting[0];
        long workedOut = counting[1];

        assertTrue(workedOut > 0, "the model has choices a comparison is read through");
        assertTrue(workedOut * 2 <= asked, () -> "asked " + asked + " times and worked out "
                + workedOut + ": each place a choice is read in is asked of by more than two"
                + " readings of a comparison on this chain");
    }
}
