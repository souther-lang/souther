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
    private final Map<Derivation, Proposition> concluded = new IdentityHashMap<>();
    private int unread;

    /** A concluding of a condition at {@code where}, where the reader knows it. */
    public Conclusion(Optional<ModelOccurrence> where) {
        this.where = where;
    }

    /** What {@code step} concludes. */
    public Proposition of(Derivation step) {
        Proposition out = step.conclusion(this);
        concluded.put(step, out);
        return out;
    }

    /** What {@code step} concluded the last time it was concluded here, or null where it was not. */
    public Proposition concludedAt(Derivation step) {
        return concluded.get(step);
    }

    Proposition unread(Derivation.Stopped stopped) {
        return new Proposition.Unread(where, unread++, stopped.why(), stopped.fixed(), true);
    }
}
