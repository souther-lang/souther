package souther.compiler.observe;

import java.math.BigDecimal;
import java.time.Duration;

/**
 * A wait, as a report writes it.
 *
 * <p>What a run is held to is a length, and a length is what crosses every boundary between the
 * policy that states it and the report that quotes it. Which unit a reader sees is this, and it is
 * here rather than at each place that writes a sentence, because a reader comparing two sentences
 * about the same wait is comparing this compiler with itself.
 *
 * <p>Milliseconds, which is what the sentences are written in. A wait shorter than one is written as
 * the fraction of one it is: the policy admits any positive length, and a positive wait written as
 * none says the run was given no time at all — which is a different thing, and one the policy
 * refuses outright.
 */
public final class WaitShown {

    private static final BigDecimal MILLIS_A_SECOND = BigDecimal.valueOf(1000L);

    /**
     * {@code wait} in milliseconds, without a trailing zero and without rounding a positive wait to
     * none.
     *
     * <p>Read off what a length is made of rather than converted to a number of anything. A
     * {@code Duration} holds more than a {@code long} of nanoseconds can, and more than a
     * {@code long} of milliseconds can, so writing one through either would refuse to write some of
     * the waits the policy admits — at one end by rounding a wait to none, at the other by not
     * fitting at all. Seconds and the nanoseconds beside them always fit, and the sum of the two is
     * exact.
     */
    public static String of(Duration wait) {
        return BigDecimal.valueOf(wait.getSeconds()).multiply(MILLIS_A_SECOND)
                .add(BigDecimal.valueOf(wait.getNano(), 6))
                .stripTrailingZeros().toPlainString();
    }

    private WaitShown() {
    }
}
