package souther.compiler.inputs;

import souther.compiler.types.BindingId;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * The names a reading asked of the values an application handed.
 *
 * <p>A reading inside another asks what it asks for the outer one too, and in a chain of readings
 * the set one asks is the names under it, so it is as large as the chain is deep. Passed on, it is
 * taken in by reference: the names of a watch are the ones it read itself and the sets of the
 * readings it took in, and nothing is written out until a question needs the names one by one.
 *
 * <p>The questions that do are which of them were not handed again on the way ({@link #without})
 * and whether one name is among them ({@link #contains}). The names are then worked out as one set,
 * once for each set asked, and kept; a set that adds nothing to the largest one it took in is that
 * set. What is taken in is never filtered inside another set: a set with names left out is a set of
 * its own, so what a set holds does not depend on the way it was reached, and a set shared by many
 * readings is worked out once however many ways lead to it.
 *
 * <p>Immutable: the reading that made it has ended, and no set is changed once it is held.
 */
final class AskedNames {

    /** A reading that asked of no name. */
    static final AskedNames NONE = new AskedNames(Set.of(), List.of(), Set.of());

    /** Where a test counts the names handled to work sets out (first), the steps an environment's
     *  handed values were compared on (second), the sets a watch took in (third) and the steps
     *  walked up a chain of applications (fourth), and null everywhere else. */
    static long[] COUNTING;

    static void counted(int which, int by) {
        long[] counting = COUNTING;
        if (counting != null) {
            counting[which] += by;
        }
    }

    /** The names read by the watch that made this, itself. */
    private final Set<BindingId> own;
    /** The sets of the readings it took in, none of them without a name. */
    private final List<AskedNames> parts;
    /** All of the names, or null until a question asks for them. */
    private volatile Set<BindingId> all;
    private final boolean named;

    private AskedNames(Set<BindingId> own, List<AskedNames> parts, Set<BindingId> all) {
        this.own = own;
        this.parts = parts;
        this.all = all;
        this.named = !own.isEmpty() || !parts.isEmpty() || (all != null && !all.isEmpty());
    }

    /** The set of a watch that read {@code own} itself, and which it hands on and does not change,
     *  and took in {@code parts}. */
    static AskedNames of(Set<BindingId> own, List<AskedNames> parts) {
        if (own.isEmpty()) {
            if (parts.isEmpty()) {
                return NONE;
            }
            if (parts.size() == 1) {
                return parts.get(0);
            }
        }
        return new AskedNames(own, List.copyOf(parts), parts.isEmpty() ? own : null);
    }

    private static AskedNames ofAll(Set<BindingId> all) {
        return all.isEmpty() ? NONE : new AskedNames(Set.of(), List.of(), all);
    }

    /** Whether any name was asked. Exact: a set is never taken in with none left in it. */
    boolean hasNames() {
        return named;
    }

    /** Whether {@code name} was asked. */
    boolean contains(BindingId name) {
        return own.contains(name) || all().contains(name);
    }

    /**
     * This but for {@code out}, which is this same set where none of them was asked, and a set of
     * its own where one was.
     */
    AskedNames without(Set<BindingId> out) {
        if (out.isEmpty() || !named) {
            return this;
        }
        Set<BindingId> names = all();
        boolean asked = false;
        if (out.size() <= names.size()) {
            for (BindingId each : out) {
                counted(0, 1);
                if (names.contains(each)) {
                    asked = true;
                    break;
                }
            }
        } else {
            for (BindingId each : names) {
                counted(0, 1);
                if (out.contains(each)) {
                    asked = true;
                    break;
                }
            }
        }
        if (!asked) {
            return this;
        }
        Set<BindingId> narrower = new HashSet<>(names);
        counted(0, names.size());
        narrower.removeAll(out);
        return ofAll(narrower);
    }

    /** All of the names, worked out the first time they are asked for, and the sets under this
     *  that are not worked out yet with it. */
    private Set<BindingId> all() {
        Set<BindingId> worked = all;
        if (worked != null) {
            return worked;
        }
        // Each set is worked out after the ones it took in, and once, wherever many ways lead to
        // it: a set already worked out is left as it is.
        Deque<AskedNames> pending = new ArrayDeque<>();
        pending.push(this);
        while (!pending.isEmpty()) {
            AskedNames each = pending.peek();
            if (each.all != null) {
                pending.pop();
                continue;
            }
            boolean ready = true;
            for (AskedNames part : each.parts) {
                if (part.all == null) {
                    pending.push(part);
                    ready = false;
                }
            }
            if (ready) {
                each.all = each.workedOut();
                pending.pop();
            }
        }
        return all;
    }

    /** The names, from the sets taken in having theirs: the largest of them, and what the others
     *  and the names read itself add to it, which is a copy only where something is added. */
    private Set<BindingId> workedOut() {
        Set<BindingId> largest = Set.of();
        for (AskedNames part : parts) {
            if (part.all.size() > largest.size()) {
                largest = part.all;
            }
        }
        Set<BindingId> names = largest;
        for (AskedNames part : parts) {
            if (part.all != largest) {
                names = added(names, largest, part.all);
            }
        }
        return added(names, largest, own);
    }

    /** {@code names} with what {@code more} holds, where {@code names} is {@code largest} until
     *  something is added to it, and is then a copy of its own. */
    private static Set<BindingId> added(Set<BindingId> names, Set<BindingId> largest,
                                        Set<BindingId> more) {
        Set<BindingId> wider = names;
        for (BindingId each : more) {
            counted(0, 1);
            if (!wider.contains(each)) {
                if (wider == largest) {
                    wider = new HashSet<>(largest);
                    counted(0, largest.size());
                }
                wider.add(each);
            }
        }
        return wider;
    }
}
