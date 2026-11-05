package souther.compiler.partition;

import souther.compiler.collect.SharingMap;
import souther.compiler.collect.Stacked;
import souther.compiler.numeric.WholeNumberRuns;

import java.util.List;
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
 */
final class RemaindersHeld {

    static final RemaindersHeld NONE = new RemaindersHeld(SharingMap.empty());

    /** What the statements of each remainder leave of it, shared with the ones this was made
     *  from. */
    private final SharingMap<ARemainderMoved.Unmoved, Left> held;

    private RemaindersHeld(SharingMap<ARemainderMoved.Unmoved, Left> held) {
        this.held = held;
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
        Optional<ARemainderMoved.Said> said = ARemainderMoved.saidBy(added);
        if (said.isEmpty()) {
            return new Taken.Held(this);
        }
        ARemainderMoved.Unmoved of = said.get().stated().of();
        WholeNumberRuns leaves = said.get().unmoved();
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
        return new Taken.Held(new RemaindersHeld(held.with(of, new Left(leaves, statements))));
    }
}
