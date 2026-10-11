package souther.compiler.meaning;

import java.util.concurrent.atomic.AtomicLong;

/**
 * What one walk hands its step: the value it carried there, or what a call a recursion makes of
 * itself answered. A conclusion supposes it one way or the other ({@link Conclusion#supposing}).
 *
 * <p>Told apart by the order it was made in, which no two share ({@link #made}), so two walks never
 * share one however alike they are, and a statement holding two of them keeps both.
 *
 * @param ordinal the order it was made in
 */
public record ACarriedValue(long ordinal) {

    private static final AtomicLong MADE = new AtomicLong();

    /** One no other walk carries. */
    public static ACarriedValue made() {
        return new ACarriedValue(MADE.incrementAndGet());
    }

    @Override
    public String toString() {
        return "carried#" + ordinal;
    }
}
