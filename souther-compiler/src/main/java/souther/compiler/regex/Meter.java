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
 *
 * <p><b>And which of them refused is kept, because they are not the same fact.</b> One machine over
 * the first limit is a machine somebody wrote and can write differently; a build stopped by the
 * second is one this answer had already spent its allowance on, and the same machine asked for
 * first would have been made. A caller told only that nothing came back has to guess between them,
 * and the guess it can make from what it holds is the wrong one — it names the rule it was reading.
 */
public final class Meter {

    /** Which of the two limits refused a state. */
    public enum Stopped {

        /** One machine came to more states than a machine may have. */
        ONE_MACHINE,

        /** What this answer has built came to more than it may build in all. */
        THE_ANSWER
    }

    private final int mostStates;
    private int left;
    private Stopped stopped;

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

    /**
     * Which limit refused the state that stopped the construction that just came back with nothing,
     * or null where nothing has been refused.
     *
     * <p>The last refusal, which is that construction's, because a refusal stops the construction
     * it happened in: every place a state is refused abandons what it was making there and then, so
     * a refusal recorded here has been read by the caller it belongs to before another can happen.
     *
     * <p>What is answered is which limit said no, and not what would have happened under some other
     * allowance. Working that out means building the machine a second way to see how far it gets,
     * which is the spending this exists to stop — so the question this can answer honestly is the
     * one about the limit that actually refused.
     */
    public Stopped stoppedBy() {
        return stopped;
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
            // The machine's own limit first where both are over. What is being answered is which
            // limit refused this request, and a request larger than any machine may be is one no
            // allowance would have let through — so it is that, whatever else is also true of it.
            if (many > mostStates - (long) mine) {
                stopped = Stopped.ONE_MACHINE;
                return false;
            }
            if (many > left) {
                stopped = Stopped.THE_ANSWER;
                return false;
            }
            mine += (int) many;
            left -= (int) many;
            return true;
        }
    }
}
