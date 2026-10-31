package souther.compiler.partition;

import souther.compiler.core.Core;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The state of an object that a reading depends on and the state it must leave alone, taken from
 * the roles its fields are given ({@link ReadingRole}).
 *
 * <p>Which fields those are is the table's and no hand-written list's: a field with no role stops
 * this where it is first made, so a field added to the object is classified before any reading is
 * kept or taken again, and a field the table calls an input is compared whether or not anyone
 * remembered to.
 */
final class ReadingState {

    /** A piece of state that says what has been added to it, as a value that is the same only
     *  while nothing has. */
    interface Marked {
        Object mark();
    }

    /**
     * The inputs of a reading as they stood.
     *
     * @param values what the inputs were, copied where they are collections so that a later change
     *               to the collection is not a change to this
     * @param asked  what the aggregates being read were
     */
    record Inputs(List<Object> values, Object asked) {}

    private final Field[] inputs;
    private final Field asked;
    private final Field[] guards;
    private final Field[] flags;

    ReadingState(Class<?> owner, Map<String, ReadingRole> roles) {
        List<Field> inputFields = new ArrayList<>();
        List<Field> guardFields = new ArrayList<>();
        List<Field> flagFields = new ArrayList<>();
        Field askedField = null;
        Field[] declared = owner.getDeclaredFields();
        Arrays.sort(declared, (one, other) -> one.getName().compareTo(other.getName()));
        for (Field each : declared) {
            if (Modifier.isStatic(each.getModifiers()) || each.isSynthetic()) {
                continue;
            }
            ReadingRole role = roles.get(each.getName());
            if (role == null) {
                throw new IllegalStateException("the field " + owner.getSimpleName() + "."
                        + each.getName() + " has no role in a reading kept to be taken again");
            }
            each.setAccessible(true);
            switch (role) {
                case INPUT -> inputFields.add(each);
                case FLAG -> {
                    inputFields.add(each);
                    flagFields.add(each);
                }
                case GUARDED -> {
                    inputFields.add(each);
                    guardFields.add(each);
                }
                case WRITTEN -> {
                    inputFields.add(each);
                    flagFields.add(each);
                    guardFields.add(each);
                }
                case TRIAL -> guardFields.add(each);
                case ASKED -> askedField = each;
                case FIXED, LEDGER, FOOTPRINT, BUDGET, ACCRUES, CACHE, MEMO, COUNTER -> { }
            }
        }
        this.inputs = inputFields.toArray(Field[]::new);
        this.flags = flagFields.toArray(Field[]::new);
        this.guards = guardFields.toArray(Field[]::new);
        this.asked = askedField;
    }

    /** The inputs of {@code owner} as they stand. */
    Inputs inputsOf(Object owner) {
        List<Object> values = new ArrayList<>(inputs.length);
        for (Field each : inputs) {
            Object value = read(each, owner);
            values.add(isFlag(each) ? Boolean.valueOf(value != null) : copyOf(value));
        }
        return new Inputs(Collections.unmodifiableList(values),
                asked == null ? null : copyOf(read(asked, owner)));
    }

    private boolean isFlag(Field field) {
        for (Field each : flags) {
            if (each == field) {
                return true;
            }
        }
        return false;
    }

    /** Whether {@code now} are the inputs {@code then} were; those of the aggregates only where
     *  the reading {@code then} was of asked after them. */
    boolean sameInputs(Inputs then, Inputs now, boolean askedMatters) {
        for (int at = 0; at < inputs.length; at++) {
            if (!same(then.values().get(at), now.values().get(at))) {
                return false;
            }
        }
        return !askedMatters || same(then.asked(), now.asked());
    }

    /** What the state a reading must leave alone is, to be compared with it afterwards. */
    List<Object[]> guardsOf(Object owner) {
        List<Object[]> out = new ArrayList<>(guards.length);
        for (Field each : guards) {
            Object value = read(each, owner);
            Object held = value instanceof Deque<?> deque ? deque.peek() : value;
            out.add(new Object[] {held, witnessOf(held)});
        }
        return out;
    }

    /** Whether the state a reading must leave alone is as {@code then} found it. */
    boolean sameGuards(List<Object[]> then, List<Object[]> now) {
        for (int at = 0; at < then.size(); at++) {
            Object[] before = then.get(at);
            Object[] after = now.get(at);
            if (before[0] != after[0] || !Objects.equals(before[1], after[1])) {
                return false;
            }
        }
        return true;
    }

    private static Object witnessOf(Object value) {
        return switch (value) {
            case null -> null;
            case Marked marked -> marked.mark();
            case Collection<?> collection -> collection.size();
            case Map<?, ?> map -> map.size();
            default -> null;
        };
    }

    private static Object read(Field field, Object owner) {
        try {
            return field.get(owner);
        } catch (IllegalAccessException e) {
            throw new IllegalStateException(field.getName(), e);
        }
    }

    /** A copy of {@code value} that a later change to it does not reach, where it is something
     *  that is changed. */
    private static Object copyOf(Object value) {
        return switch (value) {
            case null -> null;
            case IdentityHashMap<?, ?> map -> new Identities(map);
            case Set<?> set -> set.isEmpty() ? Set.of() : new HashSet<>(set);
            case Map<?, ?> map -> map.isEmpty() ? Map.of() : new HashMap<>(map);
            case Collection<?> collection ->
                    collection.isEmpty() ? List.of() : new ArrayList<>(collection);
            default -> value;
        };
    }

    /** Two of these held the same, a node of the core only where it is the same node. */
    private static boolean same(Object then, Object now) {
        if (then == now) {
            return true;
        }
        if (then == null || now == null || then instanceof Core) {
            return false;
        }
        return then.equals(now);
    }

    /** The entries of a map kept by identity, which are the same only where they are the same
     *  entries. */
    private record Identities(Object[] entries) {

        Identities(IdentityHashMap<?, ?> map) {
            this(flatten(map));
        }

        private static Object[] flatten(IdentityHashMap<?, ?> map) {
            Object[] out = new Object[map.size() * 2];
            int at = 0;
            for (Map.Entry<?, ?> each : map.entrySet()) {
                out[at++] = each.getKey();
                out[at++] = each.getValue();
            }
            return out;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof Identities that) || that.entries.length != entries.length) {
                return false;
            }
            for (int at = 0; at < entries.length; at++) {
                if (entries[at] != that.entries[at]) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public int hashCode() {
            return entries.length;
        }
    }
}
