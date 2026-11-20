package souther.compiler.inputs;

import java.util.Collection;
import java.util.StringJoiner;

/**
 * Why a stop is not shown, each reason once: asked whether there is one and whether one is among
 * them, and never handed out as a plurality, since nothing says them in an order of their own.
 * Held as one bit for each reason, so there is no plurality inside to iterate in an order either.
 */
public final class ReasonsAStopIsNotShown {

    static {
        if (WhyAStopIsNotShown.values().length > Integer.SIZE) {
            throw new IllegalStateException("one bit for each reason a stop is not shown, and "
                    + WhyAStopIsNotShown.values().length + " reasons");
        }
    }

    private final int held;

    private ReasonsAStopIsNotShown(int held) {
        this.held = held;
    }

    /** These reasons, each once. */
    public static ReasonsAStopIsNotShown of(Collection<WhyAStopIsNotShown> reasons) {
        int held = 0;
        for (WhyAStopIsNotShown each : reasons) {
            held |= bitOf(each);
        }
        return new ReasonsAStopIsNotShown(held);
    }

    private static int bitOf(WhyAStopIsNotShown reason) {
        return 1 << reason.ordinal();
    }

    /** Whether there is no reason. */
    public boolean isEmpty() {
        return held == 0;
    }

    /** Whether {@code reason} is one of them. */
    public boolean includes(WhyAStopIsNotShown reason) {
        return (held & bitOf(reason)) != 0;
    }

    /** These and {@code other}'s, each once. */
    public ReasonsAStopIsNotShown and(ReasonsAStopIsNotShown other) {
        return new ReasonsAStopIsNotShown(held | other.held);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof ReasonsAStopIsNotShown that && held == that.held;
    }

    @Override
    public int hashCode() {
        return held;
    }

    /** The reasons in the order they are declared, for a reader of a failed check. */
    @Override
    public String toString() {
        StringJoiner out = new StringJoiner(", ", "[", "]");
        for (WhyAStopIsNotShown each : WhyAStopIsNotShown.values()) {
            if (includes(each)) {
                out.add(each.name());
            }
        }
        return out.toString();
    }
}
