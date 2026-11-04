package souther.compiler.partition;

import souther.compiler.numeric.WholeNumberRuns;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
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
 */
final class RemaindersHeld {

    static final RemaindersHeld NONE = new RemaindersHeld(Map.of());

    /** What the statements of each remainder leave of it, never changed once made. */
    private final Map<ARemainderMoved.Unmoved, Left> held;

    private RemaindersHeld(Map<ARemainderMoved.Unmoved, Left> held) {
        this.held = held;
    }

    /** What the statements of a remainder leave of it, and the statements. */
    record Left(WholeNumberRuns remainders, List<RowDemand.OnARemainder> statements) {

        Left {
            statements = List.copyOf(statements);
        }
    }

    /** What taking a statement in came to. */
    sealed interface Taken {

        /** The statements are held together; this is what they leave. */
        record Held(RemaindersHeld remainders) implements Taken {}

        /** The statements of the one remainder, the last of them the one taken in, leave none of
         *  it. */
        record NoneLeft(List<RowDemand.OnARemainder> statements) implements Taken {}
    }

    /** What the statements of each remainder leave of it, without the statements: two of these
     *  leaving the same are the same to whatever is taken in next. */
    Map<ARemainderMoved.Unmoved, WholeNumberRuns> left() {
        Map<ARemainderMoved.Unmoved, WholeNumberRuns> out = new HashMap<>();
        held.forEach((of, each) -> out.put(of, each.remainders()));
        return Collections.unmodifiableMap(out);
    }

    /** These with {@code added} taken in, or the statements of its remainder where they leave
     *  none of it. */
    Taken taking(RowDemand.OnARemainder added) {
        Optional<ARemainderMoved> stated = ARemainderMoved.of(added);
        if (stated.isEmpty()) {
            return new Taken.Held(this);
        }
        ARemainderMoved.Unmoved of = stated.get().of();
        WholeNumberRuns leaves = stated.get().unmoved(added.leaves());
        Left before = held.get(of);
        List<RowDemand.OnARemainder> statements = new ArrayList<>();
        if (before != null) {
            statements.addAll(before.statements());
            leaves = leaves.and(before.remainders());
        }
        statements.add(added);
        if (leaves.isNone()) {
            return new Taken.NoneLeft(statements);
        }
        Map<ARemainderMoved.Unmoved, Left> out = new HashMap<>(held);
        out.put(of, new Left(leaves, statements));
        return new Taken.Held(new RemaindersHeld(Collections.unmodifiableMap(out)));
    }
}
