package souther.compiler.inputs;

import souther.compiler.collect.InTheOrderGiven;
import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * Which element of each container something was read of, by the names that stand for it.
 *
 * <p>A position inside a container's elements, {@code xs[*].n}, says an element and not which one,
 * so two names for two elements of {@code xs} read {@code n} at one position. What tells them apart
 * is the name, and past the reading of a condition the name is gone from what the condition
 * states. This is the name, kept beside what was stated, for a reader that has to know whether two
 * statements at one position are about one value.
 *
 * <p>Only what the names say. Two names may be handed one element on some run, so two names are
 * never a proof that two values differ; one name is one value.
 *
 * @param named for each container and part of an entry, the names it was read through, in the
 *              order met. Empty where nothing was read through a name for an element
 */
public record ElementsNamed(Map<Slot, Set<BindingId>> named) {

    /** Read through no name for an element. */
    public static final ElementsNamed NONE = new ElementsNamed(Map.of());

    /**
     * Which element of a container: the container and the part of the entry. The key and the value
     * of one entry are two names for one element, and are two slots.
     */
    public record Slot(InputReads.ContainerOf container, HeldIn.Part part) {

        public Slot {
            Objects.requireNonNull(container, "an element is of some container");
            Objects.requireNonNull(part, "an element is the element or the key of its entry");
        }
    }

    /** One name standing for an element at {@code slot}. */
    public record Named(Slot slot, BindingId name) {

        public Named {
            Objects.requireNonNull(slot, "a name stands for an element of some container");
            Objects.requireNonNull(name, "an element is stood for by some name");
        }
    }

    public ElementsNamed {
        Map<Slot, Set<BindingId>> copy = new LinkedHashMap<>();
        named.forEach((slot, names) -> {
            if (names.isEmpty()) {
                throw new IllegalArgumentException("a slot read is read through some name: "
                        + slot);
            }
            copy.put(slot, InTheOrderGiven.set(names));
        });
        named = InTheOrderGiven.map(copy);
    }

    /** What {@code names}, in the order met, say. */
    public static ElementsNamed of(List<Named> names) {
        if (names.isEmpty()) {
            return NONE;
        }
        Map<Slot, Set<BindingId>> out = new LinkedHashMap<>();
        for (Named each : names) {
            out.computeIfAbsent(each.slot(), _ -> new LinkedHashSet<>()).add(each.name());
        }
        return new ElementsNamed(out);
    }

    /** These and {@code other}, each slot with the names of both. */
    public ElementsNamed and(ElementsNamed other) {
        if (other.named.isEmpty()) {
            return this;
        }
        if (named.isEmpty()) {
            return other;
        }
        Map<Slot, Set<BindingId>> out = new LinkedHashMap<>();
        named.forEach((slot, names) -> out.put(slot, new LinkedHashSet<>(names)));
        other.named.forEach((slot, names) ->
                out.computeIfAbsent(slot, _ -> new LinkedHashSet<>()).addAll(names));
        return new ElementsNamed(out);
    }

    /** These, with only the names {@code of} holds: a slot left with no name is left out. */
    public ElementsNamed keepingTheNamesOf(ElementsNamed of) {
        if (named.isEmpty()) {
            return this;
        }
        Set<BindingId> kept = new LinkedHashSet<>();
        of.named.values().forEach(kept::addAll);
        Map<Slot, Set<BindingId>> out = new LinkedHashMap<>();
        named.forEach((slot, names) -> {
            Set<BindingId> left = new LinkedHashSet<>(names);
            left.retainAll(kept);
            if (!left.isEmpty()) {
                out.put(slot, left);
            }
        });
        return out.isEmpty() ? NONE : new ElementsNamed(out);
    }

    /** Whether nothing was read through a name for an element. */
    public boolean isEmpty() {
        return named.isEmpty();
    }

    /** Whether more than one name stood for one element here: what was read is of no one value
     *  at that element's positions. */
    public boolean readsTwoAtOnce() {
        for (Set<BindingId> each : named.values()) {
            if (each.size() > 1) {
                return true;
            }
        }
        return false;
    }

    /** Whether {@code name} stood for an element of some container here. */
    public boolean stoodFor(BindingId name) {
        for (Set<BindingId> each : named.values()) {
            if (each.contains(name)) {
                return true;
            }
        }
        return false;
    }
}
