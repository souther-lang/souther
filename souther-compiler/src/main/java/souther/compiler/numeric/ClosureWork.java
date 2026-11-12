package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.List;

/**
 * What the rounds of a closure worked out ({@link RoundWork}), kept so that the closure of the same
 * rules with more rules after them need not work it out again.
 *
 * <p>How a closure was computed and never what it is: {@link ClosedState} holds what the rules
 * leave, and two closures of equal rules are equal whether or not either was worked out from this.
 * Held by {@link ClosedStates} for the few closures asked last and let go after, so that a closure
 * whose work has been let go is followed by a closure worked out in full, which is the same closure.
 *
 * @param <A> what a position of the rules is
 */
final class ClosureWork<A> {

    private final List<RoundWork<A>> rounds = new ArrayList<>();

    /** The work of the next round, which started in {@code ends} over {@code rules}. */
    RoundWork<A> next(List<AffineConstraint<A>> rules, Box<A> ends) {
        RoundWork<A> round = new RoundWork<>(rules, ends);
        rounds.add(round);
        return round;
    }

    /** The work of round {@code at}, or null where the closure ran no such round or kept none of it. */
    RoundWork<A> round(int at) {
        return at < rounds.size() ? rounds.get(at) : null;
    }

    /** The work of the last round the closure ran, or null where it ran none. */
    RoundWork<A> last() {
        return rounds.isEmpty() ? null : rounds.getLast();
    }

    /** How many premises, over all the rounds, were moved from the work before rather than summed. */
    long moved() {
        long moved = 0;
        for (RoundWork<A> each : rounds) {
            moved += each.moved;
        }
        return moved;
    }
}
