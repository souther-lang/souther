package souther.compiler.check;

import souther.compiler.types.BindingId;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

/**
 * One walk that reads through the names of an expression: the names it is inside, and what each name
 * it has read came to.
 *
 * <p>The first is what stops a name that reaches itself. The second is what stops a name read twice
 * from being read twice: what a binding comes to is a fact about the value it was given and the
 * environment that value is read in, and both are fixed where the binding was made (ADR-0111) — so
 * the second reading of a name is the first reading asked again. A body naming one binding twice,
 * over a chain of bindings that each do, is a reading that doubles with every link without it.
 *
 * <p>Held for one walk and not beyond it. What a name comes to is that reading's answer, and a table
 * outliving the walk would be one reading's answer offered to another's. Which is why this is not
 * held by the environment that answers what a name was given: that answers every reader the same,
 * and what each of them makes of it is theirs.
 *
 * <p>A name is entered on the way to its own answer, so what is held under it was reached with it on
 * the path. That is the same path every reading of it takes: a path can hold a binding twice only
 * where a value reaches itself, which is refused before any of this runs.
 *
 * <p>What this does not know is what a reading makes of a name. A reader that reads a name
 * differently each time it stands somewhere — one for which the second occurrence means something
 * the first did not — is not a reader to hold one of these, and says so where it does not.
 *
 * @param <T> what the reading answers for a name
 */
class BindingWalk<T> {

    private final Set<BindingId> following = new HashSet<>();
    private final Map<BindingId, T> read;

    BindingWalk() {
        this.read = new HashMap<>();
    }

    /**
     * A walk begun from inside another's, for a reading that is asked a question of its own while it
     * is reading: the names it is inside are this one's, since a name being read is not on the path
     * of a question about something else, and what has been read is the other's, since it is the
     * same reading and the same names. Left to start empty, a reading that asks itself about a name
     * it is part way through reading would read it again from the beginning, and so would every
     * question that one asks.
     */
    BindingWalk(BindingWalk<T> reading) {
        this.read = reading.read;
    }

    /** Whether {@code binding} may be followed from here, marking it followed where it may. */
    boolean enter(BindingId binding) {
        return following.add(binding);
    }

    /** Done following {@code binding}. */
    void leave(BindingId binding) {
        following.remove(binding);
    }

    /**
     * What {@code binding} came to, asking {@code answer} the first time and no other. An answer of
     * null is not held: it says the reading did not come to anything, and is asked again.
     */
    T readingOf(BindingId binding, Supplier<T> answer) {
        T already = read.get(binding);
        if (already != null) {
            return already;
        }
        T came = answer.get();
        if (came != null) {
            read.put(binding, came);
        }
        return came;
    }
}
