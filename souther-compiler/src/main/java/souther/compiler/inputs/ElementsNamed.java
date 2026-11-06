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
 * @param named   for each container and part of an entry, the names it was read through, in the
 *                order met. Empty where nothing was read through a name for an element
 * @param unnamed the elements read through a name whose element is not known: what was read at
 *                one of these is of no one value there, as what two names were read through is
 */
public record ElementsNamed(Map<Slot, Set<BindingId>> named, Set<Slot> unnamed) {

    /** Read through no name for an element. */
    public static final ElementsNamed NONE = new ElementsNamed(Map.of(), Set.of());

    /**
     * Which element of a container: the container and the part of the entry. The key and the value
     * of one entry are two names for one element, and are two slots.
     */
    public record Slot(InputReads.ContainerOf container, HeldIn.Part part) {

        public Slot {
            Objects.requireNonNull(container, "an element is of some container");
            Objects.requireNonNull(part, "an element is the element or the key of its entry");
        }

        /**
         * The innermost element of a container of the input {@code position} is in, or null where
         * it is in none.
         *
         * <p>The one place a position is said to be in an element: both where a name for an
         * element is filed and where what was read at a position asks which name stood for it,
         * so that the two cannot part.
         */
        public static Slot innermostOf(TermPath position) {
            List<TermPath.Step> steps = position.steps();
            for (int at = steps.size() - 1; at >= 0; at--) {
                HeldIn.Part part = switch (steps.get(at)) {
                    case TermPath.Step.Element _ -> HeldIn.Part.ELEMENT;
                    case TermPath.Step.Key _ -> HeldIn.Part.KEY;
                    case TermPath.Step.Field _, TermPath.Step.Refine _ -> null;
                };
                if (part != null) {
                    return new Slot(new InputReads.ContainerOf.AtAPosition(position.prefix(at)),
                            part);
                }
            }
            return null;
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
        unnamed = InTheOrderGiven.set(unnamed);
    }

    /** What {@code names}, in the order met, say, where every element was read through a name
     *  that is known to stand for it — as what a statement was told is. */
    public static ElementsNamed of(List<Named> names) {
        return of(names, Set.of());
    }

    /** What {@code names}, in the order met, say, and the elements {@code unnamed} read through
     *  a name whose element is not known. */
    public static ElementsNamed of(List<Named> names, Set<Slot> unnamed) {
        if (names.isEmpty() && unnamed.isEmpty()) {
            return NONE;
        }
        Map<Slot, Set<BindingId>> out = new LinkedHashMap<>();
        for (Named each : names) {
            out.computeIfAbsent(each.slot(), _ -> new LinkedHashSet<>()).add(each.name());
        }
        return new ElementsNamed(out, unnamed);
    }

    /** These and {@code other}, each slot with the names of both. */
    public ElementsNamed and(ElementsNamed other) {
        if (other.isEmpty()) {
            return this;
        }
        if (isEmpty()) {
            return other;
        }
        Map<Slot, Set<BindingId>> out = new LinkedHashMap<>();
        named.forEach((slot, names) -> out.put(slot, new LinkedHashSet<>(names)));
        other.named.forEach((slot, names) ->
                out.computeIfAbsent(slot, _ -> new LinkedHashSet<>()).addAll(names));
        Set<Slot> notKnown = new LinkedHashSet<>(unnamed);
        notKnown.addAll(other.unnamed);
        return new ElementsNamed(out, notKnown);
    }

    /** These, with only the names {@code of} holds: a slot left with no name is left out. An
     *  element read through a name not known to stand for it stays so. */
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
        return out.isEmpty() && unnamed.isEmpty() ? NONE : new ElementsNamed(out, unnamed);
    }

    /** Whether nothing was read through a name for an element. */
    public boolean isEmpty() {
        return named.isEmpty() && unnamed.isEmpty();
    }

    /** Whether what was read at {@code slot} is of no one value there: more than one name stood
     *  for the element, or a name whose element is not known. */
    public boolean noOneValueAt(Slot slot) {
        Set<BindingId> names = named.get(slot);
        return unnamed.contains(slot) || (names != null && names.size() > 1);
    }

    /** Whether what was read at some element is of no one value there ({@link #noOneValueAt}). */
    public boolean readsNoOneValue() {
        if (!unnamed.isEmpty()) {
            return true;
        }
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
