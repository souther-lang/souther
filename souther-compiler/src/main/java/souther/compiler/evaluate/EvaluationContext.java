package souther.compiler.evaluate;

import souther.runtime.WorkCheckpoint;

/**
 * What one evaluation is allowed, counted by the code as it runs.
 *
 * <p>This class is the compiler's, not the runtime's, for the reason {@link
 * souther.compiler.coverage.Probe} is: code generated for an evaluation calls
 * {@code souther.compiler.evaluate.EvaluationContext.tick}, and the loader that runs it delegates
 * every name it does not hold to its parent, whose chain ends at the compiler's own loader — so the
 * call resolves while evaluating and there is nothing to resolve anywhere else. Shipped classes are
 * generated without the calls, so a jar never refers to this.
 *
 * <p>The state is per thread because an evaluation is per thread. Two rows evaluated on two workers
 * are two evaluations, and a shared counter would let one row spend another's budget — which is the
 * thing this exists to stop, in the form it is hardest to see.
 *
 * <p>Counted rather than timed, and that is the whole of the difference: how many counted points the
 * code went through is a property of what it did, so it is the same on a fast machine and a slow one,
 * on a quiet host and a loaded one. How long it took is a property of the machine.
 */
public final class EvaluationContext {

    /** What the thread running an evaluation has left. Null between evaluations: a tick with nothing
     * counting is a call from code nobody is holding to a budget, and ignoring it is right. */
    private static final ThreadLocal<State> CURRENT = new ThreadLocal<>();

    /**
     * One evaluation's remaining budget and how deep it currently is.
     *
     * <p>Also the checkpoint a runtime operation called from the evaluation passes, so a step spent
     * inside the operation is spent from this evaluation's budget and from no other: the operation
     * holds the state it was handed, and not whichever evaluation the thread is running when it
     * passes.
     */
    private static final class State implements WorkCheckpoint {
        private long remainingSteps;
        private int depth;
        private final int depthLimit;

        State(long steps, int depthLimit) {
            this.remainingSteps = steps;
            this.depthLimit = depthLimit;
        }

        @Override
        public void pass() {
            stopIfAbandoned();
            if (--remainingSteps < 0) {
                throw StepLimitExceeded.INSTANCE;
            }
        }

        /** {@code pieces} steps at once. Where the budget does not hold them all it is left spent out,
         *  as a pass past its end leaves it, and what they would have paid for does not start. */
        @Override
        public void spend(long pieces) {
            stopIfAbandoned();
            if (pieces > remainingSteps) {
                remainingSteps = -1;
                throw StepLimitExceeded.INSTANCE;
            }
            remainingSteps -= pieces;
        }
    }

    /**
     * Starts counting on this thread, for an evaluation allowed {@code steps} and {@code depthLimit}.
     *
     * <p>Called by the compiler around one row, never by generated code.
     */
    public static void begin(long steps, int depthLimit) {
        CURRENT.set(new State(steps, depthLimit));
    }

    /**
     * One counted point, passed.
     *
     * <p>Public and static because that is what an {@code invokestatic} from generated code needs.
     * Throws when the budget is gone, which is how the evaluated code stops itself: nothing outside it
     * can, so nothing outside it has to be waiting to.
     */
    public static void tick() {
        State state = CURRENT.get();
        if (state != null) {
            state.pass();
        }
    }

    /**
     * What a runtime operation called from evaluated code passes as it works: one of its passes is
     * one {@link #tick}, spent from the same budget.
     *
     * <p>Asked once where the operation is called, so the operation's own loop passes it without
     * looking up whose evaluation it is each time round. {@link WorkCheckpoint#NONE} where nothing
     * is counting, for the same reason a tick then does nothing.
     */
    public static WorkCheckpoint checkpoint() {
        State state = CURRENT.get();
        return state == null ? WorkCheckpoint.NONE : state;
    }

    /**
     * Entering a recursive helper.
     *
     * <p>Counted separately from {@link #tick} because a recursion that does not stop and a loop that
     * does not stop are different things to be told about: one is answered by making the recursion
     * structural, the other by bounding the loop. It also has to be reached before the stack runs out,
     * which is what makes it a count rather than a wait for {@link StackOverflowError}.
     */
    public static void enter() {
        State state = CURRENT.get();
        if (state == null) {
            return;
        }
        stopIfAbandoned();
        if (++state.depth > state.depthLimit) {
            throw DepthLimitExceeded.INSTANCE;
        }
        if (--state.remainingSteps < 0) {
            throw StepLimitExceeded.INSTANCE;
        }
    }

    /**
     * Stops the evaluated code when whoever is waiting for it has given up.
     *
     * <p>The wait for a row is on the clock, and what it does when it runs out is interrupt the
     * worker. An interrupt is only a request, and evaluated code that reaches no blocking call
     * never sees it, so a worker whose row was given up on would go on spending CPU and heap for as
     * long as the JVM lives. The counted points are the one place every evaluation passes through,
     * in the generated code and inside the runtime operations it calls, so the request is read here.
     */
    private static void stopIfAbandoned() {
        if (Thread.currentThread().isInterrupted()) {
            throw EvaluationAbandoned.INSTANCE;
        }
    }

    /** Leaving a recursive helper, however it leaves — the generated method returns through this on
     * its normal paths and on its exceptional one. */
    public static void leave() {
        State state = CURRENT.get();
        if (state != null) {
            state.depth--;
        }
    }

    /** How many of the steps this evaluation was given are gone. Read after it ends, for a report
     * that says what a row actually cost. */
    public static long spent(long allowed) {
        State state = CURRENT.get();
        return state == null ? 0L : allowed - Math.max(state.remainingSteps, 0L);
    }

    /** Stops counting, and lets go of the state. A worker thread outlives the evaluation it ran, so
     * state left behind would be the next evaluation's starting point. */
    public static void end() {
        CURRENT.remove();
    }

    /**
     * Whether {@code thrown} is the evaluated code having stopped itself.
     *
     * <p>Asked wherever something catches broadly enough to catch this. Evaluating a fixture is full
     * of places that read a failure as "that value cannot be built" — which is the right reading for
     * almost everything, and the wrong one for this: the value was fine, the evaluation ran out. A
     * report that took one for the other names the wrong thing and tells the author to change
     * something that is not wrong.
     */
    public static boolean overspending(Throwable thrown) {
        return thrown instanceof StepLimitExceeded || thrown instanceof DepthLimitExceeded
                || thrown instanceof EvaluationAbandoned;
    }

    private EvaluationContext() {}
}
