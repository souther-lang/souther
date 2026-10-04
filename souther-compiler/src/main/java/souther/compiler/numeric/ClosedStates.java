package souther.compiler.numeric;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Function;

/**
 * Where a closure is worked out, and for how long one is kept to stand for the next question equal
 * to it.
 *
 * <p>A domain keeps what its own rules leave once it has been asked. What it cannot see is another
 * domain holding the same rules — and a reader that builds a domain per question builds that one
 * over and over, through different contexts that leave the numbers the same and through readings
 * made from one another. So the closure is asked of one of these, which a domain carries and lends
 * to every domain made from it.
 *
 * <p><b>What a closure is, is the arithmetic's to say; how long one is kept is the owner's.</b> Two
 * questions are one closure where they are equal ({@link ClosureQuestion}), and nothing here or in
 * the owner decides that. What the owner decides is the lifetime: it makes one of these where the
 * repetition it wants shared lives and drops it with whatever holds it. Everything else asks
 * {@link #NONE}, which keeps nothing, and is where a reader stays until somebody has measured a
 * repetition it owns.
 *
 * <p>Carried and not part of what a domain is. Two domains holding the same rules are the same
 * domain whichever of these they carry; what differs is only whether working the rules out is done
 * again.
 *
 * <p>Asked from any thread a reading is asked from. A closure worked out twice by two threads that
 * met at one question is the same closure, so either may be the one kept.
 */
public final class ClosedStates {

    /** Nothing kept: every domain works out what its rules leave for itself. */
    public static final ClosedStates NONE = new ClosedStates(null, null);

    /** One closure per question, kept for as long as whatever holds this is held. */
    public static ClosedStates kept() {
        return new ClosedStates(new ConcurrentHashMap<>(), new ConcurrentHashMap<>());
    }

    private final Map<ClosureQuestion<?>, ClosedState<?>> answers;

    /**
     * Where each order puts each set of positions it has been asked about
     * ({@link ClosureQuestion#placesIn}).
     *
     * <p>Kept because putting a question to the table means stating it, and stating it means
     * sorting the positions its rules weigh — with a comparison that can be dear, once per question
     * asked and not once per closure worked out. The positions repeat far more than the rules do.
     *
     * <p>Keyed by the order as the object it is, which is not what makes two questions one: two
     * orders written apart that put the positions in the same places are two entries here and one
     * question at {@link #answers}. An entry missed is a sort done again and nothing else.
     */
    private final Map<CanonicalOrder<?>, Map<Set<?>, Map<?, Integer>>> places;

    private final AtomicLong workedOut = new AtomicLong();

    private ClosedStates(Map<ClosureQuestion<?>, ClosedState<?>> answers,
                         Map<CanonicalOrder<?>, Map<Set<?>, Map<?, Integer>>> places) {
        this.answers = answers;
        this.places = places;
    }

    /** What {@code rules} leave, spaced by {@code spacing} and walked in {@code order}. */
    <A> ClosedState<A> of(List<AffineConstraint<A>> rules, Function<A, Granularity> spacing,
                          CanonicalOrder<A> order) {
        if (answers == null) {
            return ClosedState.of(ClosureQuestion.of(rules, spacing, order));
        }
        ClosureQuestion<A> question =
                ClosureQuestion.of(rules, spacing, weighed -> placed(weighed, order));
        // The cast holds because an entry is only ever put under the question it answers, and a
        // question over positions of type A is answered by a closure over the same positions.
        @SuppressWarnings("unchecked")
        ClosedState<A> had = (ClosedState<A>) answers.get(question);
        if (had != null) {
            return had;
        }
        // Worked out outside the table: a closure takes long enough that holding the table while
        // it is worked out would stop every other question waiting on it.
        ClosedState<A> made = ClosedState.of(question);
        workedOut.incrementAndGet();
        @SuppressWarnings("unchecked")
        ClosedState<A> raced = (ClosedState<A>) answers.putIfAbsent(question, made);
        return raced == null ? made : raced;
    }

    /** {@link ClosureQuestion#placesIn}, kept for the order and the positions it was asked of. */
    private <A> Map<A, Integer> placed(Set<A> positions, CanonicalOrder<A> order) {
        Map<Set<?>, Map<?, Integer>> under =
                places.computeIfAbsent(order, unused -> new ConcurrentHashMap<>());
        // The cast holds because an entry is only ever put under the positions it places.
        @SuppressWarnings("unchecked")
        Map<A, Integer> had = (Map<A, Integer>) under.get(positions);
        if (had != null) {
            return had;
        }
        Map<A, Integer> made = ClosureQuestion.placesIn(positions, order);
        @SuppressWarnings("unchecked")
        Map<A, Integer> raced = (Map<A, Integer>) under.putIfAbsent(Set.copyOf(positions), made);
        return raced == null ? made : raced;
    }

    /**
     * How many closures this has worked out rather than lent, for a test holding a reader to sharing
     * them. Nought for {@link #NONE}, which lends nothing and counts nothing.
     *
     * <p>Counted rather than timed: what is held is that a question asked again is not worked out
     * again, which is a shape and not a speed.
     */
    public long workedOut() {
        return workedOut.get();
    }
}
