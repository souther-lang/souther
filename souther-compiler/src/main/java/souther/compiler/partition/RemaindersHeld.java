package souther.compiler.partition;

import souther.compiler.collect.SharingMap;
import souther.compiler.collect.Stacked;
import souther.compiler.numeric.WholeNumberRuns;

import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The statements of remainders a way has taken in, each held to what it leaves of the remainder
 * of its form unmoved.
 *
 * <p>Statements of one remainder of a form, moved by whatever numbers ({@link ARemainderMoved}),
 * leave of it where each of them holds at once. A statement that is of no remainder read as one
 * with others is not taken in: none of those is shown to leave anything, and leaving them out
 * proves nothing about the way. A form weighed otherwise, or divided by another number, is another
 * remainder, and nothing is said of the two together.
 *
 * <p>A way's walk holds these for each alternative it takes, so a statement taken in makes another
 * of these and leaves the one it was taken into as it was.
 *
 * <p>A walk takes one statement in along every way of the choices before it, and what the
 * statement says of its remainder is the statement's alone. So what each statement says is read
 * once a walk, by the statement, and held by every one of these made from the walk's
 * {@link #none}: one walk's, and so one thread's.
 */
final class RemaindersHeld {

    /** What the statements of each remainder leave of it, shared with the ones this was made
     *  from. */
    private final SharingMap<ARemainderMoved.Unmoved, Left> held;

    /** What each statement taken in on this walk says of its remainder, by the statement: empty
     *  where it is of no remainder read as one with others. */
    private final Map<RowDemand.OnARemainder, Optional<Read>> read;

    private RemaindersHeld(SharingMap<ARemainderMoved.Unmoved, Left> held,
                           Map<RowDemand.OnARemainder, Optional<Read>> read) {
        this.held = held;
        this.read = read;
    }

    /** Nothing taken in, at the start of one walk. */
    static RemaindersHeld none() {
        return new RemaindersHeld(SharingMap.empty(), new IdentityHashMap<>());
    }

    /** What a statement says of its remainder: the remainder of its form unmoved and what it
     *  leaves of that. */
    private record Read(ARemainderMoved.Unmoved of, WholeNumberRuns leaves) {

        /** What {@code statement} says, or empty where it is of no remainder read as one with
         *  others. */
        static Optional<Read> of(RowDemand.OnARemainder statement) {
            return ARemainderMoved.of(statement)
                    .map(stated -> new Read(stated.of(), stated.unmoved(statement.leaves())));
        }
    }

    /** What the statements of a remainder leave of it, and the statements, which are written out
     *  only where they leave none. */
    private record Left(WholeNumberRuns remainders, Stacked<RowDemand.OnARemainder> statements) {}

    /** What taking a statement in came to. */
    sealed interface Taken {

        /** The statements are held together; this is what they leave. */
        record Held(RemaindersHeld remainders) implements Taken {}

        /** The statements of the one remainder, the last of them the one taken in, leave none of
         *  it. */
        record NoneLeft(List<RowDemand.OnARemainder> statements) implements Taken {}
    }

    /** These with {@code added} taken in, or the statements of its remainder where they leave
     *  none of it. */
    Taken taking(RowDemand.OnARemainder added) {
        Optional<Read> stated = read.computeIfAbsent(added, Read::of);
        if (stated.isEmpty()) {
            return new Taken.Held(this);
        }
        ARemainderMoved.Unmoved of = stated.get().of();
        WholeNumberRuns leaves = stated.get().leaves();
        Left before = held.get(of);
        Stacked<RowDemand.OnARemainder> statements = Stacked.empty();
        if (before != null) {
            statements = before.statements();
            leaves = leaves.and(before.remainders());
        }
        statements = statements.then(added);
        if (leaves.isNone()) {
            return new Taken.NoneLeft(statements.inOrder());
        }
        return new Taken.Held(new RemaindersHeld(held.with(of, new Left(leaves, statements)),
                read));
    }
}
