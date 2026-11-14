package souther.compiler.inputs;

import souther.compiler.types.BindingId;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

/**
 * The names a reading asked of the values an application handed, as the names read directly and
 * the sets of the readings inside it, each with the names handed again on the way to it.
 *
 * <p>A reading inside another asks what it asks for the outer one too, and in a chain of readings
 * the set one asks is the names under it, so it is as large as the chain is deep. A set that is
 * written out again for every reading it passes through is that size each time. Here it is held
 * by reference, and what it holds is worked out where it is asked ({@link #contains}), which is
 * for the few names two applications hand differently and not for the names asked.
 *
 * <p>Immutable once made: the reading that made it has ended.
 */
final class AskedNames {

    /** Where a test counts the names looked at to place a set taken in (first) and the sets
     *  walked to answer whether a name was asked (second), and the sets taken in (third), and
     *  null everywhere else. */
    static long[] COUNTING;

    static void counted(int which, int by) {
        long[] counting = COUNTING;
        if (counting != null) {
            counting[which] += by;
        }
    }

    /** A reading that asked of no name. */
    static final AskedNames NONE = new AskedNames(Set.of(), List.of());

    /** The names of {@code names} but for {@code without}, which are the ones handed again on the
     *  way from where the set was asked to where it is taken in. */
    record Part(AskedNames names, Set<BindingId> without) {}

    private final Set<BindingId> own;
    private final List<Part> parts;

    AskedNames(Set<BindingId> own, List<Part> parts) {
        this.own = own;
        this.parts = parts;
    }

    /** What a watch that read {@code own} itself and took in {@code parts} asked. */
    static AskedNames of(Set<BindingId> own, List<Part> parts) {
        if (own.isEmpty()) {
            if (parts.isEmpty()) {
                return NONE;
            }
            if (parts.size() == 1 && parts.get(0).without().isEmpty()) {
                return parts.get(0).names();
            }
        }
        return new AskedNames(own, List.copyOf(parts));
    }

    /** Whether any name was asked. Exact: a part is kept only where some name is left in it. */
    boolean hasNames() {
        return !own.isEmpty() || !parts.isEmpty();
    }

    /** Whether {@code name} was asked. */
    boolean contains(BindingId name) {
        if (own.contains(name)) {
            return true;
        }
        if (parts.isEmpty()) {
            return false;
        }
        return reaches(name);
    }

    private boolean reaches(BindingId name) {
        Set<AskedNames> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        Deque<AskedNames> pending = new ArrayDeque<>();
        pending.push(this);
        seen.add(this);
        while (!pending.isEmpty()) {
            AskedNames each = pending.pop();
            counted(1, 1);
            if (each.own.contains(name)) {
                return true;
            }
            for (Part part : each.parts) {
                if (!part.without().contains(name) && seen.add(part.names())) {
                    pending.push(part.names());
                }
            }
        }
        return false;
    }

    /** Whether some name asked is not one of {@code without}. */
    boolean hasANameOutside(Set<BindingId> without) {
        Set<AskedNames> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        return outsideIn(this, without, seen);
    }

    private static boolean outsideIn(AskedNames names, Set<BindingId> without,
                                     Set<AskedNames> seen) {
        if (!seen.add(names)) {
            return false;
        }
        for (BindingId each : names.own) {
            counted(0, 1);
            if (!without.contains(each)) {
                return true;
            }
        }
        for (Part part : names.parts) {
            if (part.without().isEmpty()) {
                if (outsideIn(part.names(), without, seen)) {
                    return true;
                }
            } else {
                // What was seen was seen under the names left out so far, which this part adds to.
                Set<BindingId> both = new HashSet<>(without);
                both.addAll(part.without());
                if (outsideIn(part.names(), both,
                        Collections.newSetFromMap(new IdentityHashMap<>()))) {
                    return true;
                }
            }
        }
        return false;
    }
}
