package souther.compiler.check;

import souther.compiler.types.BindingId;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

/**
 * One walk that reads through the names of an expression: the names it is inside, and what each
 * name it has read came to.
 *
 * <p>The first is what stops a name that reaches itself. The second is what stops a name read twice
 * from being read twice: a body naming one binding twice, over a chain of bindings that each do, is
 * a reading that doubles with every link without it.
 *
 * <p>What is held is keyed by the question and nothing looser: the binding, the value it was
 * given, and the environment that value is read in, the last two as the objects they are. A name
 * read again is the same question exactly where all three are the same (ADR-0111), and then the
 * answer is the same whoever asks it, so the table may be handed to another walk of the same
 * reading ({@link Answers}) — a reading that asks itself about a value part way through reading it
 * reads it once.
 *
 * <p>A name is entered on the way to its own answer, so what is held under it was reached with it on
 * the path. That is the same path every reading of it takes: a path can hold a binding twice only
 * where a value reaches itself, which is refused before any of this runs.
 *
 * <p>What this does not know is what a reading makes of a name. A reader that reads a name
 * differently each time it stands somewhere — one for which the second occurrence means something
 * the first did not — is not a reader to hold one of these.
 *
 * @param <T> what the reading answers for a name
 */
class BindingWalk<T> {

    private final Set<BindingId> following = new HashSet<>();
    private final Answers<T> read;

    /** A walk with a table of its own. */
    BindingWalk() {
        this(new Answers<>());
    }

    /** A walk reading into {@code read}, which other walks of the same reading share. */
    BindingWalk(Answers<T> read) {
        this.read = read;
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
     * What {@code binding}, given {@code value} and read in {@code at}, came to, asking
     * {@code answer} the first time and no other. An answer of null is not held: it says the
     * reading did not come to anything, and is asked again.
     */
    T readingOf(BindingId binding, Object value, Object at, Supplier<T> answer) {
        Asked asked = new Asked(binding, value, at);
        T already = read.answered.get(asked);
        if (already != null) {
            return already;
        }
        T came = answer.get();
        if (came != null) {
            read.answered.put(asked, came);
        }
        return came;
    }

    /**
     * What one reading's names came to, for every walk of that reading.
     *
     * <p>Held as long as whoever holds it reads with one reading, and handed to no other: what a
     * name comes to is that reading's answer.
     */
    static final class Answers<T> {
        private final Map<Asked, T> answered = new HashMap<>();
    }

    /** A name, the value it was given and the environment it is read in; the last two by what
     *  object they are, since the question is about these and not about ones equal to them. */
    private static final class Asked {
        private final BindingId binding;
        private final Object value;
        private final Object at;

        Asked(BindingId binding, Object value, Object at) {
            this.binding = binding;
            this.value = value;
            this.at = at;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Asked asked && asked.binding.equals(binding)
                    && asked.value == value && asked.at == at;
        }

        @Override
        public int hashCode() {
            return 31 * (31 * binding.hashCode() + System.identityHashCode(value))
                    + System.identityHashCode(at);
        }
    }
}
