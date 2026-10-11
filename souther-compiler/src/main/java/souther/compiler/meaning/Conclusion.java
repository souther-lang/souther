package souther.compiler.meaning;

import souther.compiler.types.ModelOccurrence;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

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
 *
 * <p><b>And under what it supposes of the values walks carried.</b> A walk's step is read once,
 * with what the walk carried into it standing as itself, and concluded once for each way that
 * value is supposed to have come out ({@link #supposing}). A step that never reads a carried value
 * concludes the same under every supposition, so it is concluded once for all of them: what is
 * kept of a step is the suppositions it read, and it is taken again wherever those are the same.
 * Concluded where nothing supposes it, a carried value is itself ({@link Proposition.Carried}): a
 * part read, which a walk deciding how it closes takes either way.
 */
public final class Conclusion {

    /** What every concluding made from one by supposing more shares: where, the numbering, and
     *  what each step came to. */
    private static final class Shared {
        private final Optional<ModelOccurrence> where;
        private final boolean reusing;
        private final Map<Derivation, List<Kept>> kept = new IdentityHashMap<>();
        private final Map<Derivation, Proposition> last = new IdentityHashMap<>();
        /** The carried values each step being concluded has read so far, innermost last. */
        private final Deque<Set<ACarriedValue>> reading = new ArrayDeque<>();
        private int unread;

        private Shared(Optional<ModelOccurrence> where, boolean reusing) {
            this.where = where;
            this.reusing = reusing;
        }
    }

    /** What a step came to, and how each carried value it read was supposed then — absent where
     *  nothing supposed it. */
    private record Kept(Map<ACarriedValue, Optional<Boolean>> read, Proposition concluded) {}

    private final Shared shared;
    private final Map<ACarriedValue, Boolean> supposed;

    /** A concluding of a condition at {@code where}, where the reader knows it. */
    public Conclusion(Optional<ModelOccurrence> where) {
        this(new Shared(where, false), Map.of());
    }

    private Conclusion(Shared shared, Map<ACarriedValue, Boolean> supposed) {
        this.shared = shared;
        this.supposed = supposed;
    }

    /**
     * A concluding that concludes each step once, however many derivations it is asked of hold it.
     *
     * <p>For asking what the candidates for one expression state while a reading tries them, where
     * each candidate holds the steps of the parts under it and those were concluded when the parts
     * were read: a derivation is a value, so what a step concludes under one supposition does not
     * change. The parts left unread are numbered here as they are first met and not again, which
     * is no numbering of a condition — what such a concluding is good for is what is stated, and
     * not which number a part nothing read is given.
     */
    public static Conclusion reusing() {
        return new Conclusion(new Shared(Optional.empty(), true), Map.of());
    }

    /** This concluding, with what {@code carried} stands for supposed to have come out as
     *  {@code holds}. */
    public Conclusion supposing(ACarriedValue carried, boolean holds) {
        Map<ACarriedValue, Boolean> more = new HashMap<>(supposed);
        more.put(Objects.requireNonNull(carried, "a supposition is of some carried value"), holds);
        return new Conclusion(shared, Map.copyOf(more));
    }

    /** What {@code step} concludes. */
    public Proposition of(Derivation step) {
        if (shared.reusing) {
            for (Kept each : shared.kept.getOrDefault(step, List.of())) {
                if (agrees(each.read())) {
                    readAll(each.read().keySet());
                    return each.concluded();
                }
            }
        }
        shared.reading.push(new HashSet<>());
        Proposition out;
        Set<ACarriedValue> read;
        try {
            out = step.conclusion(this);
        } finally {
            read = shared.reading.pop();
        }
        if (shared.reusing) {
            Map<ACarriedValue, Optional<Boolean>> how = new HashMap<>();
            read.forEach(each -> how.put(each, Optional.ofNullable(supposed.get(each))));
            shared.kept.computeIfAbsent(step, _ -> new ArrayList<>())
                    .add(new Kept(Map.copyOf(how), out));
        }
        readAll(read);
        shared.last.put(step, out);
        return out;
    }

    /** What {@code how} concludes, beside {@code how}: the one way a meaning is made. */
    public MeaningsOfABody.Meaning meaningOf(Derivation how) {
        return new MeaningsOfABody.Meaning(of(how), how);
    }

    /** What {@code step} concluded the last time it was concluded here, or null where it was not. */
    public Proposition concludedAt(Derivation step) {
        return shared.last.get(step);
    }

    Proposition unread(Derivation.Stopped stopped) {
        return new Proposition.Unread(shared.where, shared.unread++, stopped.why(),
                stopped.fixed(), true);
    }

    /** What {@code carried} is supposed to have come out as, or itself where nothing supposes it. */
    Proposition carried(ACarriedValue carried) {
        readAll(Set.of(carried));
        Boolean holds = supposed.get(carried);
        return holds != null ? new Proposition.Always(holds) : new Proposition.Carried(carried, true);
    }

    /** Whether each carried value {@code read} says how it was supposed is supposed so here. */
    private boolean agrees(Map<ACarriedValue, Optional<Boolean>> read) {
        for (Map.Entry<ACarriedValue, Optional<Boolean>> each : read.entrySet()) {
            if (!each.getValue().equals(Optional.ofNullable(supposed.get(each.getKey())))) {
                return false;
            }
        }
        return true;
    }

    /** That the step being concluded read {@code carried}. */
    private void readAll(Set<ACarriedValue> carried) {
        Set<ACarriedValue> into = shared.reading.peek();
        if (into != null) {
            into.addAll(carried);
        }
    }
}
