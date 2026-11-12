package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.IntPredicate;

/**
 * What one round of a closure worked out of the premises it held, kept so that the same round of the
 * closure of the same rules with more rules after them need not work it out again.
 *
 * <p>How a closure was computed and never what it is. {@link ClosedState} holds what the rules
 * leave; this holds, for each question the round asked of {@link FormReach}, what every premise of
 * that round came to, against the ends the round started in. A round that has these from the same
 * round of the closure of the rules before its own takes each of those answers over to its own ends
 * by what the ends that moved did to it ({@link #endsThatMoved}), and works out only the premises
 * the added rules gave. What comes back is what working every premise out would have come to, so a
 * round with no work to start from, or with work it cannot use, is the same round.
 *
 * @param <A> what a position of the rules is
 */
final class RoundWork<A> {

    /** A place holding no candidate: the premise is a rule the question leaves out. */
    static final byte ABSENT = 0;

    /** A place holding the sum a premise's residual comes to, and how it was reached. */
    static final byte SUMMED = 1;

    /** A place holding no candidate: the premise names none of the question's positions, so what
     *  it leaves is the question beside it and is read, or passed over, from the ends as they are
     *  when it is asked. */
    static final byte UNNAMED = 3;

    /** A place whose candidate is worked out again each time it is read: a residual of two
     *  positions, which the closed differences may bound, or a sum the exact arithmetic could not
     *  hold. */
    static final byte ASKED = 2;

    /**
     * What each premise of a round leaves of one question, by the place of the premise.
     *
     * <p>A residual is a sum of one end per position it weighs. Held as the sum, how many of its
     * ends are missing and how many are not reached, so that moving one end moves the sum, the
     * count of missing ends and the count of ends not reached by that end alone.
     */
    static final class Candidates {

        final byte[] kinds;
        final ExactRatio[] sums;
        final int[] withoutEnd;
        final int[] notReached;

        Candidates(int places) {
            kinds = new byte[places];
            sums = new ExactRatio[places];
            withoutEnd = new int[places];
            notReached = new int[places];
        }

        int places() {
            return kinds.length;
        }
    }

    private final List<AffineConstraint<A>> rules;
    private final Box<A> ends;
    private int premises = -1;

    /** How many premises of this round were moved from the work before rather than summed. */
    long moved;

    private final Map<AffineConstraint<A>, Map<CanonicalForm<A>, Map<A, Candidates>>> asked =
            new IdentityHashMap<>();

    private final Map<AffineConstraint<A>, Candidates[]> wholes = new IdentityHashMap<>();

    private final IntPredicate room;

    /** A round that keeps whatever it is asked. */
    RoundWork(List<AffineConstraint<A>> rules, Box<A> ends) {
        this(rules, ends, _ -> true);
    }

    /**
     * @param rules the rules the round read, in the order it read them
     * @param ends  the ends the round started in
     * @param room  whether this many more places may be kept, which it counts them against if so
     */
    RoundWork(List<AffineConstraint<A>> rules, Box<A> ends, IntPredicate room) {
        this.rules = rules;
        this.ends = ends;
        this.room = room;
    }

    /** How many premises the round held, set once it has built them. */
    void premisesHeld(int count) {
        premises = count;
    }

    int premises() {
        return premises;
    }

    Box<A> ends() {
        return ends;
    }

    /**
     * Whether {@code more} is these rules with others after them, the very rules in the same
     * order — which is what makes the places of the premises these rules gave the places of the
     * first premises of {@code more}.
     */
    boolean precedes(List<AffineConstraint<A>> more) {
        if (more.size() < rules.size() || premises < 0) {
            return false;
        }
        for (int at = 0; at < rules.size(); at++) {
            if (more.get(at) != rules.get(at)) {
                return false;
            }
        }
        return true;
    }

    /** What the round left of the question for {@code atom} in {@code half} of {@code rule}, or
     *  null where it was not asked. */
    Candidates of(AffineConstraint<A> rule, CanonicalForm<A> half, A atom) {
        Map<CanonicalForm<A>, Map<A, Candidates>> halves = asked.get(rule);
        if (halves == null) {
            return null;
        }
        Map<A, Candidates> atoms = halves.get(half);
        return atoms == null ? null : atoms.get(atom);
    }

    /** What the round left of the whole form of {@code rule}, for its upper end ({@code 0}) or its
     *  lower one ({@code 1}), or null where it was not asked. */
    Candidates whole(AffineConstraint<A> rule, int direction) {
        Candidates[] held = wholes.get(rule);
        return held == null ? null : held[direction];
    }

    /** Keeps what the round left of the whole form, unless the closure has no room for it. */
    void putWhole(AffineConstraint<A> rule, int direction, Candidates candidates) {
        if (!room.test(candidates.places())) {
            return;
        }
        wholes.computeIfAbsent(rule, _ -> new Candidates[2])[direction] = candidates;
    }

    /** Keeps what the round left of one question, unless the closure has no room for it. */
    void put(AffineConstraint<A> rule, CanonicalForm<A> half, A atom, Candidates candidates) {
        if (!room.test(candidates.places())) {
            return;
        }
        asked.computeIfAbsent(rule, _ -> new HashMap<>())
                .computeIfAbsent(half, _ -> new HashMap<>())
                .put(atom, candidates);
    }

    /**
     * The positions whose ends are not what {@code now} has them, or null where there are more than
     * {@code most} of them.
     *
     * <p>A position is moved where either of its ends is another cut or is missing where it was not
     * or the other way round. Taken over every position either box has an end for: a position
     * neither has an end for is read the same by both.
     */
    List<A> endsThatMoved(Box<A> now, int most) {
        Set<A> positions = new HashSet<>(ends.atLeast().keySet());
        positions.addAll(ends.atMost().keySet());
        positions.addAll(now.atLeast().keySet());
        positions.addAll(now.atMost().keySet());
        List<A> apart = new ArrayList<>();
        for (A position : positions) {
            if (!Objects.equals(ends.leastOf(position), now.leastOf(position))
                    || !Objects.equals(ends.mostOf(position), now.mostOf(position))) {
                if (apart.size() == most) {
                    return null;
                }
                apart.add(position);
            }
        }
        return apart;
    }
}
