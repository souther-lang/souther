package souther.compiler.regex;

/**
 * What this compiler is allowed to build while working one answer out, counted as it is built.
 *
 * <p>Before the state is made and not after it. A machine put together and then measured is a
 * machine this compiler already paid for — the memory was taken, the loops were run — and saying it
 * was too big at that point is a report rather than a limit. So every place a state is made asks
 * here first, and a construction refused is one that stopped where it was.
 *
 * <p><b>The one place work is counted.</b> What an operation will cost was worked out in two
 * places once, each with a formula of its own, and a formula is a guess about an implementation:
 * a product of two machines is at most the product of their sizes and is usually far less, so a
 * caller refusing on the formula refuses answers it could afford, and one charging the formula
 * charges for states nobody made. Counted here, what is spent is what was built.
 *
 * <p>Two limits, because two things can go wrong. One machine may be larger than anything this
 * will hold, and a great many small ones may be more than it will do in all — a plan of cheap meets
 * is affordable at every step and not as a whole.
 */
public final class Meter {

    private final int mostStates;
    private int left;

    /**
     * @param mostStates how many states one machine may hold
     * @param mostBuilt how many states everything this meter is for may make between them, the
     *                  machines thrown away on the way included
     */
    public Meter(int mostStates, int mostBuilt) {
        if (mostStates <= 0 || mostBuilt <= 0) {
            throw new IllegalArgumentException("a meter allows something");
        }
        this.mostStates = mostStates;
        this.left = mostBuilt;
    }

    /** How much of the whole allowance is left, which is what a caller reports having spent. */
    public int left() {
        return left;
    }

    /** One machine about to be made, counting its own states as well as this meter's. */
    Making making() {
        return new Making();
    }

    /**
     * What one machine has taken so far.
     *
     * <p>Its own count beside the meter's, because the two limits are about different things: this
     * one is how large a single machine may be, and the meter's is how much making them all may
     * take. A machine is abandoned by its builder returning nothing, and what it spent stays spent
     * — the states were made.
     */
    final class Making {

        private int mine;

        /** Whether one more state may be made, and it is counted where the answer is yes. */
        boolean state() {
            return states(1);
        }

        /**
         * The same for {@code many} at once, for a builder that knows its size before it starts.
         *
         * <p>Asked before the first of them is made. A product of two machines knows how many
         * states it will have, and allocating them to find out that they were too many is the
         * thing this exists to stop.
         */
        boolean states(long many) {
            if (many < 0) {
                throw new IllegalArgumentException("a machine is made of no fewer than no states");
            }
            if (many > mostStates - (long) mine || many > left) {
                return false;
            }
            mine += (int) many;
            left -= (int) many;
            return true;
        }
    }
}
