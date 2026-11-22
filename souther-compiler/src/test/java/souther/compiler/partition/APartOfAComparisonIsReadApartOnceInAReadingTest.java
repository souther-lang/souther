package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A part of a comparison asked to be read apart from the rest is read once in one reading of it,
 * whoever asks for it.
 *
 * <p>What a run works out to give a name its value is asked of each part of that value, and a part
 * is made of the names before it. Read for itself by every part that reaches it, a name at the
 * bottom of a chain is read once for each way down the chain.
 */
class APartOfAComparisonIsReadApartOnceInAReadingTest {

    private static final String CHAIN = """
            module m

            let quotient (a: Int, b: Int): Int =
                match Int.truncatingDivide(a, b) with
                    | Int as n -> n
                    | DivisionByZero -> unreachable "a number written out"

            let taken (left: Int, by: Int, held: Int): Int = {
                let wanted = quotient(left, by)
                if wanted < held then wanted else held
            }

            behavior paid : (sum: Int, a: Int, b: Int) -> Bool
            let paid (sum, a, b) = {
                let first = taken(sum, 50, a)
                let left1 = sum - first * 50
                let second = taken(left1, 10, b)
                left1 - second * 10 == 0
            }
            """;

    @Test
    void aPartAskedAgainIsNotReadAgain() {
        long[] counting = {0, 0};
        AffineReading.PARTS = counting;
        try {
            ACompiledModel.measured(CHAIN, new Adequacy.Asked(Adequacy.Level.OFF, false));
        } finally {
            AffineReading.PARTS = null;
        }
        long asked = counting[0];
        long read = counting[1];

        assertTrue(read > 0, "the model has parts read apart");
        assertTrue(read * 3 <= asked * 2, () -> "asked " + asked + " times and read " + read
                + ": of every three times a part is asked for on this chain, one at least is of a"
                + " part read before");
    }
}
