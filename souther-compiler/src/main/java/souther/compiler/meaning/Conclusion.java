package souther.compiler.meaning;

import souther.compiler.types.ModelOccurrence;

import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Optional;

/**
 * One concluding of a derivation: what each of its steps comes to, with the parts nothing read
 * numbered in the order they are met.
 *
 * <p>The numbers are given here and not where the reading stopped. A reading may try more than one
 * rule at a place and keep one, and a part a rule it did not keep stopped at was never part of what
 * is stated — numbered as it was met, it would move the number of every part after it.
 *
 * <p>Kept by step, by identity, because a step and its conclusion are what a reader of where each
 * part was read off asks about: two steps alike in every component are still two places in the
 * condition.
 */
public final class Conclusion {

    private final Optional<ModelOccurrence> where;
    private final boolean reusing;
    private final Map<Derivation, Proposition> concluded = new IdentityHashMap<>();
    private int unread;

    /** A concluding of a condition at {@code where}, where the reader knows it. */
    public Conclusion(Optional<ModelOccurrence> where) {
        this(where, false);
    }

    private Conclusion(Optional<ModelOccurrence> where, boolean reusing) {
        this.where = where;
        this.reusing = reusing;
    }

    /**
     * A concluding that concludes each step once, however many derivations it is asked of hold it.
     *
     * <p>For asking what the candidates for one expression state while a reading tries them, where
     * each candidate holds the steps of the parts under it and those were concluded when the parts
     * were read: a derivation is a value, so what a step concludes does not change. The parts left
     * unread are numbered here as they are first met and not again, which is no numbering of a
     * condition — what such a concluding is good for is what is stated, and not which number a part
     * nothing read is given.
     */
    public static Conclusion reusing() {
        return new Conclusion(Optional.empty(), true);
    }

    /** What {@code step} concludes. */
    public Proposition of(Derivation step) {
        if (reusing) {
            Proposition before = concluded.get(step);
            if (before != null) {
                return before;
            }
        }
        Proposition out = step.conclusion(this);
        concluded.put(step, out);
        return out;
    }

    /** What {@code how} concludes, beside {@code how}: the one way a meaning is made. */
    public MeaningsOfABody.Meaning meaningOf(Derivation how) {
        return new MeaningsOfABody.Meaning(of(how), how);
    }

    /** What {@code step} concluded the last time it was concluded here, or null where it was not. */
    public Proposition concludedAt(Derivation step) {
        return concluded.get(step);
    }

    Proposition unread(Derivation.Stopped stopped) {
        return new Proposition.Unread(where, unread++, stopped.why(), stopped.fixed(), true);
    }
}
