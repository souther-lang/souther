package souther.compiler.check;

import souther.compiler.numeric.ClosedStates;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * What {@link Known#reachesNothing} answered of each state the readers of one engine asked, so that
 * a state asked again from any of them is answered from what was worked out the first time.
 *
 * <p><b>What the answer is, is {@link Known}'s; how long one is kept is the owner's.</b> This decides
 * nothing about a state: every answer here is the one {@link Known#reachesNothing} gives, asked once.
 * What the owner decides is the lifetime — {@link PathEngine} makes one of these and every reader
 * under it asks it, and it goes with the engine. Everything else asks {@link #NONE}, which keeps
 * nothing, as {@link ClosedStates} does for the closures a domain works out.
 *
 * <p><b>Kept by the state object, not by what it holds.</b> The readers on one walk ask the very
 * state they were handed, again and again, from each place that wants to know whether to go on; that
 * is the repetition this saves. Two states holding the same are two questions here, which costs a
 * second working out and never a wrong answer, and asking a state's equality would be to walk its
 * components for a question that does not need them.
 *
 * <p>Of the constraints and of nothing else in a {@link Known}, since that is all the answer reads
 * ({@link ConstraintState#leavesNoRow()}).
 *
 * <p>Asked from any thread a reading is asked from. An answer worked out twice by two threads that
 * met at one state is the same answer.
 */
final class ReachabilityAnswers {

    /** Nothing kept: every state is asked again. */
    static final ReachabilityAnswers NONE = new ReachabilityAnswers(null);

    /** One answer per state asked, for as long as whatever holds this is held. */
    static ReachabilityAnswers kept() {
        return new ReachabilityAnswers(new ConcurrentHashMap<>());
    }

    /** A state, told from every other by being that object. */
    private record Asked(ConstraintState<?> state) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Asked that && state == that.state;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(state);
        }
    }

    private final Map<Asked, Boolean> answers;

    private ReachabilityAnswers(Map<Asked, Boolean> answers) {
        this.answers = answers;
    }

    /** {@link Known#reachesNothing} of {@code known}. */
    boolean reachesNothing(Known known) {
        return answers == null ? known.reachesNothing()
                : answers.computeIfAbsent(new Asked(known.constraints()),
                        _ -> known.reachesNothing());
    }
}
