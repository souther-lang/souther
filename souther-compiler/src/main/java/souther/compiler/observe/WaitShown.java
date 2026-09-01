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

    /** Above this a wait is written whole, and nanoseconds of it are not worth counting — nor
     *  representable, past the point {@link Duration#toNanos} overflows. */
    private static final long WHOLE_ABOVE_SECONDS = 3600L;

    /** {@code wait} in milliseconds, without a trailing zero and without rounding a positive wait
     *  to none. */
    public static String of(Duration wait) {
        if (wait.getSeconds() > WHOLE_ABOVE_SECONDS) {
            return Long.toString(wait.toMillis());
        }
        return BigDecimal.valueOf(wait.toNanos(), 6).stripTrailingZeros().toPlainString();
    }

    private WaitShown() {
    }
}
