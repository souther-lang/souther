package souther.compiler.coverage;

/**
 * The two ways a walk is rewritten.
 *
 * <p>A walk threads what its step answers into the step on the next element, so what it answers
 * rests on two things no row of fewer than two elements reads: that it goes on past the first
 * element, and that each step reads what the step before it answered. A row of no element runs no
 * step and a row of one element runs the step once on the seed, and both come out the same whether
 * or not either is so. Each rewrite takes one of the two away, and each is an edit an author could
 * make: walking only the first element of the list, and handing the step the seed where it is handed
 * what it carries.
 *
 * <p>Two and not one, because a step that never reads what it carries is the walk under another
 * spelling once it is handed the seed, and still walks every element: only stopping after one step
 * tells it from a walk that does not.
 */
public enum WalkRewrite {

    /** The walk stops after its first step, and answers what that step answered. */
    STOPS_AFTER_ONE_STEP(0),

    /** Every step is handed the seed in the place of what the step before it answered. */
    STEPS_FROM_THE_SEED(1);

    private final int code;

    WalkRewrite(int code) {
        this.code = code;
    }

    /**
     * The number the classes tell this rewrite by at a walk, which is what a run asks them for and
     * what the switch there compares. Written out rather than read off the order the constants are
     * declared in, since a class emitted with one number is asked with it.
     */
    public int code() {
        return code;
    }
}
