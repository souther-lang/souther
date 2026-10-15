package souther.compiler.types;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

/**
 * Copies of the model's code something was read off or met in: each once, in the order they were
 * met.
 *
 * <p>A value of its own and not a list, because each once is part of what it says, and is kept
 * where a value is made and nowhere else. A list leaves it to every writer, and one condition may
 * be written over many constructs each a copy of its own, so a writer asking a list whether it
 * holds each of them pays their number squared.
 *
 * <p>In the order met because that is the order a reader is told them in.
 *
 * @param inOrder the copies, each once, in the order they were met
 */
public record ModelOccurrences(List<ModelOccurrence> inOrder)
        implements Iterable<ModelOccurrence> {

    /** None at all. */
    public static final ModelOccurrences NONE = new ModelOccurrences(List.of());

    public ModelOccurrences {
        inOrder = List.copyOf(new LinkedHashSet<>(inOrder));
    }

    /** {@code copies}, each once, in the order given. */
    public static ModelOccurrences of(Collection<ModelOccurrence> copies) {
        return copies.isEmpty() ? NONE : new ModelOccurrences(List.copyOf(copies));
    }

    /** One copy. */
    public static ModelOccurrences of(ModelOccurrence copy) {
        return new ModelOccurrences(List.of(copy));
    }

    /** These, and then those of {@code other} not among them. */
    public ModelOccurrences and(ModelOccurrences other) {
        if (other.isEmpty()) {
            return this;
        }
        if (isEmpty()) {
            return other;
        }
        Set<ModelOccurrence> both = new LinkedHashSet<>(inOrder);
        both.addAll(other.inOrder);
        return new ModelOccurrences(List.copyOf(both));
    }

    /** Every one of {@code each}, in the order given, each copy once. */
    public static ModelOccurrences allOf(Collection<ModelOccurrences> each) {
        Gathering gathering = new Gathering();
        each.forEach(gathering::add);
        return gathering.gathered();
    }

    public boolean isEmpty() {
        return inOrder.isEmpty();
    }

    public Stream<ModelOccurrence> stream() {
        return inOrder.stream();
    }

    @Override
    public Iterator<ModelOccurrence> iterator() {
        return inOrder.iterator();
    }

    /**
     * Copies gathered a few at a time into one, each once, in the order met.
     *
     * <p>For gathering many into one: made one {@link #and} at a time, every copy gathered so far
     * would be gathered again at each.
     */
    public static final class Gathering {

        private final Set<ModelOccurrence> held = new LinkedHashSet<>();

        public Gathering add(ModelOccurrences copies) {
            held.addAll(copies.inOrder);
            return this;
        }

        public Gathering add(ModelOccurrence copy) {
            held.add(copy);
            return this;
        }

        public boolean isEmpty() {
            return held.isEmpty();
        }

        public ModelOccurrences gathered() {
            return held.isEmpty() ? NONE : new ModelOccurrences(List.copyOf(held));
        }
    }
}
