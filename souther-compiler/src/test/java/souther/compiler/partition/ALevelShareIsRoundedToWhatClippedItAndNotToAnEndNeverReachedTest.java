package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.partition.ContainersAddingUp.Ends;
import souther.compiler.partition.ContainersAddingUp.Spread;
import souther.compiler.partition.ContainersAddingUp.Split;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A LEVEL share is rounded to the width the decomposition's own {@code total} and starting point
 * were written at, widened only where an end it moved toward actually clipped a share to a
 * boundary — never from an end that was named but that no share ever reached.
 *
 * <p>An upfront width folding {@code upTo}/{@code downTo} in whether or not either is ever hit
 * used to disagree with this: {@code total} at one place and {@code from} at nought, shared over
 * three with an {@code upTo} far finer than either but never approached, once rounded three
 * shares to that finer width instead of the one place the numbers actually in play were stated
 * to.
 */
class ALevelShareIsRoundedToWhatClippedItAndNotToAnEndNeverReachedTest {

    @Test
    void anUpToNeverClippedToLeavesTheSharesAtTotalsOwnWidth() {
        BigDecimal total = new BigDecimal("1.1");
        Ends ends = new Ends(ExactRatio.ZERO, null, ExactRatio.of(new BigDecimal("1.234")),
                NumericDomain.Bounds.OPEN);

        Split split = ContainersAddingUp.splitting(total, 3, ends, Spread.LEVEL, new Carrier.Dense());

        Split.Some some = assertInstanceOf(Split.Some.class, split,
                "three shares of 1.1 from 0, never clipped to 1.234, decompose");
        assertEquals(
                List.of(new BigDecimal("0.3"), new BigDecimal("0.4"), new BigDecimal("0.4")),
                some.values(),
                "upTo is never reached by any share, so a share is rounded to the one place total"
                        + " and from were themselves written at — not to upTo's own finer scale,"
                        + " which no share here ever needed");
    }
}
